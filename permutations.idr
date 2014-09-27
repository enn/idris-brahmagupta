module permutations

import order
import fin_order

infixl 8 &

class Sortable a where
 e : a
 (&) : a -> a -> a
 
 leftId : (x : a) -> e & x = x
 rightId : (x : a) -> x & e = x
 ass : (x : a) -> (y : a) -> (z : a) -> x & (y & z) = (x & y) & z
 comm : (x : a) -> (y : a) -> x & y = y & x

evL : Sortable a => Vect n a -> List (Fin n) -> a
evL env [] = e
evL env (x :: xs) = index x env & evL env xs

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
 

insert : SpecifiedOrdering a => a -> List a -> List a
insert x [] = x :: []
insert x (y :: ys) = case compare' x y of
  LT => (x :: (y :: ys))
  EQ => (x :: (y :: ys))
  GT => (y :: (insert x ys))

intermediate_lemma : SpecifiedOrdering a =>
 (x : a) -> (t0 : a) -> (l0 : List a) ->
 (P : List a -> Type) ->
 (compare' x t0 = LT -> P (x :: (t0 :: l0))) ->
 (compare' x t0 = EQ -> P (x :: (t0 :: l0))) ->
 (compare' x t0 = GT -> P (t0 :: insert x l0)) ->
 P (insert x (t0 :: l0))
intermediate_lemma = ?p0

intermediate_lemma' : (Sortable a, SpecifiedOrdering (Fin n)) =>
 (n : Nat) -> (x : Fin n) -> (t0 : Fin n) -> (l0 : List (Fin n)) -> (env : Vect n a) ->
 (compare' x t0 = LT -> index x env & evL env (t0 :: l0) = evL env ( (x :: (t0 :: l0)))) ->
 (compare' x t0 = EQ -> index x env & evL env (t0 :: l0) = evL env ( (x :: (t0 :: l0)))) ->
 (compare' x t0 = GT -> index x env & evL env (t0 :: l0) = evL env ( (t0 :: insert x l0))) ->
 index x env & evL env (t0 :: l0) = evL env ( (insert x (t0 :: l0)))
intermediate_lemma' n x t0 l0 env = intermediate_lemma x t0 l0
  (\l' => index x env & evL env (t0 :: l0) = evL env l')

insert_spec : (Sortable a, SpecifiedOrdering (Fin n)) =>
              (env : Vect n a) ->
              (x : Fin n) -> (xs : List (Fin n)) ->
              evL env (x :: xs) = evL env (insert x xs)
insert_spec env x xs = ?p1

sort' : SpecifiedOrdering (Fin n) => List (Fin n) -> List (Fin n)
sort' [] = []
sort' (x :: xs) = insert x (sort' xs)

sort'_spec : (Sortable a, SpecifiedOrdering (Fin n)) =>
             (env : Vect n a) -> (l : List (Fin n)) ->
             evL env l = evL env (sort' l)
sort'_spec env [] = ?p2_a
sort'_spec env (x :: xs) = ?p2_b (insert_spec env x (sort' xs)) (sort'_spec env xs)


---------- Proofs ----------

permutations.p2_b = proof
  intro a,b,S1,S2,env,x,xs,T1,T2,T3,T4
  compute
  intro H1,H2
  rewrite sym H2
  rewrite sym H1
  trivial


permutations.p2_a = proof
  intros
  trivial


permutations.p1 = proof
  intro a,n,S1,S2,env,x,xs
  induction xs
  compute
  trivial
  intro t0,l0,H
  compute
  case (compare' x t0)
  compute
  trivial
  compute
  trivial
  compute
  rewrite H
  rewrite sym (ass (index x env) (index t0 env) (evL env l0))
  rewrite sym (ass (index t0 env) (index x env) (evL env l0))
  rewrite (comm (index x env) (index t0 env))
  trivial


permutations.p0 = proof
  intro a,S,x,t0,l0,P
  case (compare' x t0)
  compute
  intro H1,H2,H3
  refine H1
  trivial
  intro H1,H2,H3
  compute
  refine H2
  trivial
  intro H1,H2,H3
  compute
  refine H3
  trivial


