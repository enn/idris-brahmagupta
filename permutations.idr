module permutations

import fin_ord_theory

infixl 8 &

class Sortable a where
 e : a
 (&) : a -> a -> a
 
 leftId : (x : a) -> e & x = x
 rightId : (x : a) -> x & e = x
 ass : (x : a) -> (y : a) -> (z : a) -> x & (y & z) = (x & y) & z
 comm : (x : a) -> (y : a) -> x & y = y & x

instance [sort_plus] Sortable Nat where
 e = 0
 (&) = (+)
 
 leftId = plusZeroLeftNeutral
 rightId = plusZeroRightNeutral
 ass = plusAssociative
 comm = plusCommutative

instance [sort_times] Sortable Nat where
 e = 1
 (&) = (*)
 
 leftId = multOneLeftNeutral
 rightId = multOneRightNeutral
 ass = multAssociative
 comm = multCommutative


class HorribleUglyHack a where
 compare' : a -> a -> Ordering
 
 ord_eq_refl : (x : a) -> compare' x x = EQ
 ord_eq_symm : (x : a) -> (y : a) -> compare' x y = EQ -> compare' y x = EQ
 ord_eq_trans : (x : a) -> (y : a) -> (z : a) -> compare' x y = EQ -> compare' y z = EQ -> compare' x z = EQ
 ord_trans : (x : a) -> (y : a) -> (z : a) -> compare' x y = LT -> compare' y z = LT -> compare' x z = LT
 ord_symm : (x : a) -> (y : a) -> compare' x y = LT -> compare' y x = GT
 ord_trans' : (x : a) -> (y : a) -> (z : a) -> compare' x y = GT -> compare' y z = GT -> compare' x z = GT
 ord_symm' : (x : a) -> (y : a) -> compare' x y = GT -> compare' y x = LT

instance HorribleUglyHack (Fin n) where
 compare' = fin_compare
 ord_eq_refl = ord_eq_refl_Fin
 ord_eq_symm = ord_eq_symm_Fin
 ord_eq_trans = ord_eq_trans_Fin
 ord_trans = ord_trans_Fin
 ord_symm = ord_symm_Fin
 ord_trans' = ord_trans_Fin'
 ord_symm' = ord_symm_Fin'

evL : Sortable a => Vect n a -> List (Fin n) -> a
evL env [] = e
evL env (x :: xs) = index x env & evL env xs

insert : HorribleUglyHack fin_n => fin_n -> List fin_n -> List fin_n
insert x [] = x :: []
insert x (y :: ys) = case compare' x y of
  LT => (x :: (y :: ys))
  EQ => (x :: (y :: ys))
  GT => (y :: (insert x ys))

{-
ridiculous_lemma : (x : Fin n) -> (y : Fin n) -> (l : List (Fin n)) ->
                   (insert x (y :: ys) = (case compare' x y of
  LT => (x :: (y :: ys))
  EQ => (x :: (y :: ys))
  GT => (y :: (insert x ys))))
ridiculous_lemma x y l = refl
-}

ugly_hack_pt2 : HorribleUglyHack fin_n => (E : fin_n = Fin n) ->
                List fin_n -> List (Fin n)
ugly_hack_pt2 refl i = i

ugly_hack_pt2b : HorribleUglyHack fin_n => (E : fin_n = Fin n) ->
                 fin_n -> Fin n
ugly_hack_pt2b refl i = i

ugly_hack_pt3 : HorribleUglyHack fin_n => (E : fin_n = Fin n) ->
                (x : fin_n) -> (xs : List fin_n) ->
                ugly_hack_pt2 E (x :: xs) = ugly_hack_pt2b E x :: ugly_hack_pt2 E xs
ugly_hack_pt3 refl x xs = refl

insert_spec_hack : (HorribleUglyHack fin_n, Sortable a) =>
              (env : Vect n a) ->
              (x : fin_n) -> (xs : List (fin_n)) ->
              (E : fin_n = Fin n) ->
              evL env (ugly_hack_pt2 E (x :: xs))
              = evL env (ugly_hack_pt2 E (insert x xs))

insert_spec_hack = ?p1

insert_spec : Sortable a =>
              (env : Vect n a) ->
              (x : Fin n) -> (xs : List (Fin n)) ->
              evL env (x :: xs) = evL env (insert x xs)
insert_spec env x xs = insert_spec_hack env x xs refl

sort' : List (Fin n) -> List (Fin n)
sort' [] = []
sort' (x :: xs) = insert x (sort' xs)

sort'_spec : Sortable a => (env : Vect n a) -> (l : List (Fin n)) ->
                           evL env l = evL env (sort' l)
sort'_spec env l = ?p2

do_rearrangement : Sortable a =>
                   (env : Vect n a) -> 
                   (lhs : List (Fin n)) -> (rhs : List (Fin n)) ->
                   sort' lhs = sort' rhs ->
                   evL env lhs = evL env rhs
do_rearrangement = ?p3

example1 : (x : Nat) -> (y : Nat) -> (z : Nat) ->
 (x + (y + (z + 0))) = (y + (x + (z + 0)))
example1 x y z = do_rearrangement @{sort_plus} (x :: y :: z :: [])
                                  (fZ :: fS fZ :: fS (fS fZ) :: [])
                                   (fS fZ :: fZ :: fS (fS fZ) :: [])
                                   refl

---------- Proofs ----------

permutations.p3 = proof
  intro a,n,S,env,lhs,rhs,E
  rewrite sym (sort'_spec env lhs)
  rewrite sym (sort'_spec env rhs)
  rewrite E
  trivial


permutations.p2 = proof
  intro a,n,S,env,l
  induction l
  compute
  trivial
  intro t0,l0,E
  rewrite (insert_spec @{S} env t0 l0)
  rewrite sym (insert_spec @{S} env t0 l0)
  compute
  rewrite E
  rewrite sym E
  rewrite sym (insert_spec @{S} env t0 (sort' l0))
  trivial


permutations.p1 = proof
  intro fin_n,a,n,Hack,S,env,x,xs,E
  induction xs
  compute
  trivial
  intro t0,l0
  intro IH
  compute
  case (compare' x t0)
  compute
  trivial
  compute
  trivial
  compute
  rewrite sym (ugly_hack_pt3 E t0 (insert x l0))
  rewrite sym (ugly_hack_pt3 E x (t0 :: l0))
  rewrite sym (ugly_hack_pt3 E t0 l0)
  compute
  rewrite IH
  compute
  rewrite sym (ugly_hack_pt3 E x l0)
  compute
  rewrite sym (ass (index (ugly_hack_pt2b E x) env) (index (ugly_hack_pt2b E t0) env) (evL env (ugly_hack_pt2 E l0)))
  rewrite sym (comm (index (ugly_hack_pt2b E x) env) (index (ugly_hack_pt2b E t0) env))
  rewrite (ass (index (ugly_hack_pt2b E t0) env) (index (ugly_hack_pt2b E x) env) (evL env (ugly_hack_pt2 E l0)))
  trivial




