module order

%default total

instance Uninhabited (LT = EQ) where { uninhabited refl impossible }
instance Uninhabited (GT = EQ) where { uninhabited refl impossible }
instance Uninhabited (EQ = LT) where { uninhabited refl impossible }
instance Uninhabited (EQ = GT) where { uninhabited refl impossible }
instance Uninhabited (Prelude.Classes.LT = GT) where { uninhabited refl impossible }
instance Uninhabited (Prelude.Classes.GT = LT) where { uninhabited refl impossible }

comparing_lemma : (P : Ordering -> Type) ->
                  (z : Ordering) ->
                  P LT -> P EQ -> P GT -> P z
comparing_lemma P Prelude.Classes.LT lt eq gt = lt
comparing_lemma P EQ lt eq gt = eq
comparing_lemma P GT lt eq gt = gt

comparing_combine : Ordering -> Ordering -> Ordering
comparing_combine LT _ = LT
comparing_combine EQ r = r
comparing_combine GT _ = GT

comparing_combine_inversion_l : (x : Ordering) -> (y : Ordering) -> comparing_combine x y = EQ -> x = EQ
comparing_combine_inversion_l LT _ refl impossible
comparing_combine_inversion_l EQ LT refl impossible
comparing_combine_inversion_l EQ EQ refl = refl
comparing_combine_inversion_l EQ GT refl impossible
comparing_combine_inversion_l GT _ refl impossible

comparing_combine_inversion_r : (x : Ordering) -> (y : Ordering) -> comparing_combine x y = EQ -> y = EQ
comparing_combine_inversion_r LT _ refl impossible
comparing_combine_inversion_r EQ LT refl impossible
comparing_combine_inversion_r EQ EQ refl = refl
comparing_combine_inversion_r EQ GT refl impossible
comparing_combine_inversion_r GT _ refl impossible

comparing_combine_inversion_lt_l : (x : Ordering) -> (y : Ordering) -> comparing_combine x y = LT -> Either (x = LT) (x = EQ, y = LT)
comparing_combine_inversion_lt_l LT _ refl = Left refl
comparing_combine_inversion_lt_l EQ LT refl = Right (refl, refl)
comparing_combine_inversion_lt_l EQ EQ refl impossible
comparing_combine_inversion_lt_l EQ GT refl impossible
comparing_combine_inversion_lt_l GT _ refl impossible

comparing_combine_inversion_gt_l : (x : Ordering) -> (y : Ordering) -> comparing_combine x y = GT -> Either (x = GT) (x = EQ, y = GT)
comparing_combine_inversion_gt_l LT _ refl impossible
comparing_combine_inversion_gt_l EQ LT refl impossible
comparing_combine_inversion_gt_l EQ EQ refl impossible
comparing_combine_inversion_gt_l EQ GT refl = Right (refl, refl)
comparing_combine_inversion_gt_l GT _ refl = Left refl


class SpecifiedOrdering a where
 compare' : a -> a -> Ordering
 
 -- equivalence relation
 eq_refl : (x : a) -> compare' x x = EQ
 eq_symm : (x : a) -> (y : a) -> compare' x y = EQ -> compare' y x = EQ
 eq_trans : (x : a) -> (y : a) -> (z : a) -> compare' x y = EQ -> compare' y z = EQ -> compare' x z = EQ
 
 -- ordering relation
 ord_lt_gt : (x : a) -> (y : a) -> compare' x y = LT -> compare' y x = GT
 ord_gt_lt : (x : a) -> (y : a) -> compare' x y = GT -> compare' y x = LT
 ord_lt_eq : (x : a) -> (y : a) -> (z : a) -> compare' x y = LT -> compare' y z = EQ -> compare' x z = LT
 ord_gt_eq : (x : a) -> (y : a) -> (z : a) -> compare' x y = GT -> compare' y z = EQ -> compare' x z = GT
 ord_lt_trans : (x : a) -> (y : a) -> (z : a) -> compare' x y = LT -> compare' y z = LT -> compare' x z = LT

ord_gt_trans : SpecifiedOrdering a =>
               (x : a) -> (y : a) -> (z : a) ->
               compare' x y = GT -> compare' y z = GT -> compare' x z = GT
ord_gt_trans x y z H1 H2 = ord_lt_gt _ _ (ord_lt_trans _ _ _ (ord_gt_lt _ _ H2) (ord_gt_lt _ _ H1))

ord_eq_lt : SpecifiedOrdering a => (x : a) -> (y : a) -> (z : a) -> compare' x y = EQ -> compare' y z = LT -> compare' x z = LT
ord_eq_lt x y z H1 H2 = ord_gt_lt _ _ (ord_gt_eq _ _ _ (ord_lt_gt _ _ H2) (eq_symm _ _ H1))

ord_eq_gt : SpecifiedOrdering a => (x : a) -> (y : a) -> (z : a) -> compare' x y = EQ -> compare' y z = GT -> compare' x z = GT
ord_eq_gt x y z H1 H2 = ord_lt_gt _ _ (ord_lt_eq _ _ _ (ord_gt_lt _ _ H2) (eq_symm _ _ H1))


-- THIS (OR CONGRUENCE) NEEDS ADDED TO THE TYPECLASS
--compare_lt_eq_lemma : SpecifiedOrdering a => (x : a) -> (y : a) -> (z : a) ->
--                      compare' x y = LT -> compare' y z = EQ -> compare' x z = LT
--compare_lt_eq_lemma = ?l1

instance SpecifiedOrdering a => SpecifiedOrdering (List a) where
 compare' (x :: xs) [] = GT
 compare' [] [] = EQ
 compare' [] (y :: ys) = LT
 compare' (x :: xs) (y :: ys) = comparing_combine (compare' x y) (compare' xs ys)
 
 eq_refl [] = refl
 eq_refl (x :: xs) = ?list_prf1_2 (eq_refl xs)
 eq_symm [] [] H = ?list_prf2_1
 eq_symm [] (y :: ys) H = ?list_prf2_2
 eq_symm (x :: xs) [] H = ?list_prf2_3
 eq_symm (x :: xs) (y :: ys) H = ?list_prf2_4
   (eq_symm xs ys)
   (comparing_combine_inversion_l (compare' x y) (compare' xs ys) H)
   (comparing_combine_inversion_r (compare' x y) (compare' xs ys) H)
 eq_trans [] [] [] H1 H2 = ?list_prf3_1
 eq_trans [] [] (z :: zs) H1 H2 = ?list_prf3_2
 eq_trans [] (y :: ys) [] H1 H2 = ?list_prf3_3
 eq_trans [] (y :: ys) (z :: zs) H1 H2 = ?list_prf3_4
 eq_trans (x :: xs) [] [] H1 H2 = ?list_prf3_5
 eq_trans (x :: xs) [] (z :: zs) H1 H2 = ?list_prf3_6
 eq_trans (x :: xs) (y :: ys) [] H1 H2 = ?list_prf3_7
 eq_trans (x :: xs) (y :: ys) (z :: zs) H1 H2 = ?list_prf3_8
   (eq_trans x y z)
   (comparing_combine_inversion_l (compare' x y) (compare' xs ys) H1)
   (comparing_combine_inversion_l (compare' y z) (compare' ys zs) H2)
   (eq_trans xs ys zs)
   (comparing_combine_inversion_r (compare' x y) (compare' xs ys) H1)
   (comparing_combine_inversion_r (compare' y z) (compare' ys zs) H2)
 ord_lt_gt [] [] refl impossible
 ord_lt_gt [] (y :: ys) h = refl
 ord_lt_gt (x :: xs) [] refl impossible
 ord_lt_gt (x :: xs) (y :: ys) h = ?list_prf4_4
   (comparing_combine_inversion_lt_l (compare' x y) (compare' xs ys) h)
   (ord_lt_gt x y)
   (eq_symm x y)
   (ord_lt_gt xs ys)
 ord_gt_lt [] [] refl impossible
 ord_gt_lt [] (y :: ys) refl impossible
 ord_gt_lt (x :: xs) [] h = refl
 ord_gt_lt (x :: xs) (y :: ys) h = ?list_prf5_4
   (comparing_combine_inversion_gt_l (compare' x y) (compare' xs ys) h)
   (ord_gt_lt x y)
   (eq_symm x y)
   (ord_gt_lt xs ys)
 ord_lt_eq [] [] [] refl refl impossible
 ord_lt_eq [] [] (x :: xs) refl refl impossible
 ord_lt_eq [] (y :: ys) [] refl refl impossible
 ord_lt_eq [] (y :: ys) (x :: xs) H1 H2 = refl
 ord_lt_eq (z :: zs) [] [] refl refl impossible
 ord_lt_eq (z :: zs) [] (x :: xs) refl refl impossible
 ord_lt_eq (z :: zs) (y :: ys) [] refl refl impossible
 ord_lt_eq (z :: zs) (y :: ys) (x :: xs) H1 H2 = ?list_prf7_2
  (eq_trans z y x)
  (ord_lt_eq z y x)
  (ord_lt_eq zs ys xs)
  (comparing_combine_inversion_lt_l (compare' z y) (compare' zs ys) H1)
  (comparing_combine_inversion_l (compare' y x) (compare' ys xs) H2)
  (comparing_combine_inversion_r (compare' y x) (compare' ys xs) H2)
 ord_gt_eq [] [] [] refl refl impossible
 ord_gt_eq [] [] (x :: xs) refl refl impossible
 ord_gt_eq [] (y :: ys) [] refl refl impossible
 ord_gt_eq [] (y :: ys) (x :: xs) refl refl impossible
 ord_gt_eq (z :: zs) [] [] refl refl = refl
 ord_gt_eq (z :: zs) [] (x :: xs) refl refl impossible
 ord_gt_eq (z :: zs) (y :: ys) [] refl refl impossible
 ord_gt_eq (z :: zs) (y :: ys) (x :: xs) H1 H2 = ?list_prf7b_2
  (eq_trans z y x)
  (ord_gt_eq z y x)
  (ord_gt_eq zs ys xs)
  (comparing_combine_inversion_gt_l (compare' z y) (compare' zs ys) H1)
  (comparing_combine_inversion_l (compare' y x) (compare' ys xs) H2)
  (comparing_combine_inversion_r (compare' y x) (compare' ys xs) H2)
 ord_lt_trans [] [] [] refl refl impossible
 ord_lt_trans [] [] (z :: zs) refl refl impossible
 ord_lt_trans [] (y :: ys) [] refl refl impossible
 ord_lt_trans [] (y :: ys) (z :: zs) H1 H2 = refl
 ord_lt_trans (x :: xs) [] [] refl refl impossible
 ord_lt_trans (x :: xs) [] (z :: zs) refl refl impossible
 ord_lt_trans (x :: xs) (y :: ys) [] refl refl impossible
 ord_lt_trans (x :: xs) (y :: ys) (z :: zs) H1 H2 = ?list_prf8
  (eq_trans x y z)
  (ord_lt_eq x y z)
  (ord_lt_trans x y z)
  (ord_eq_lt x y z)
  (ord_lt_trans xs ys zs)
  (comparing_combine_inversion_lt_l (compare' x y) (compare' xs ys) H1)
  (comparing_combine_inversion_lt_l (compare' y z) (compare' ys zs) H2)

---------- Proofs ----------

order.list_prf8 = proof
  compute
  intros
  case aX5
  intro left
  case aX6
  intro left2
  rewrite sym (aX2 left left2)
  compute
  trivial
  intro right
  rewrite sym (aX1 left (fst right))
  compute
  trivial
  intro right
  case aX6
  intro left
  rewrite sym (aX3 (fst right) left)
  compute
  trivial
  intro right2
  rewrite sym (aX (fst right) (fst right2))
  compute
  rewrite (aX4 (snd right) (snd right2))
  trivial


order.list_prf7b_2 = proof
  compute
  intros
  case aX3
  intro left
  rewrite sym (aX1 left aX4)
  compute
  trivial
  intro right
  rewrite sym (aX (fst right) aX4)
  compute
  rewrite sym (aX2 (snd right) aX5)
  trivial


order.list_prf7_2 = proof
  compute
  intros
  case aX3
  intro H
  rewrite sym (aX1 H aX4)
  compute
  trivial
  intro right
  rewrite sym (aX (fst right) aX4)
  compute
  rewrite sym (aX2 (snd right) aX5)
  trivial



order.list_prf5_4 = proof
  compute
  intros
  case aX
  intro left
  rewrite sym (aX1 left)
  compute
  trivial
  intro right
  rewrite sym (aX2 (fst right))
  compute
  rewrite sym (aX3 (snd right))
  trivial


order.list_prf3_5 = proof
  compute
  intros
  trivial


order.list_prf3_1 = proof
  intros
  trivial


order.list_prf3_2 = proof
  compute
  intros
  trivial


order.list_prf3_3 = proof
  intros
  trivial


order.list_prf4_4 = proof
  intros
  case aX
  intro left
  rewrite sym (aX1 left)
  compute
  trivial
  intro right
  rewrite sym (aX2 (fst right))
  compute
  rewrite sym (aX3 (snd right))
  trivial


order.list_prf3_8 = proof
  compute
  intro a,con,cla,x,xs,y,ys,z,zs,A,B
  intro T1,T2,T3,T4,T5,T6,T7,T8,T9,T10,T11,T12
  intro A1
  intro A2
  intro A3
  intro B1
  intro B2
  intro B3
  rewrite sym (A1 A2 A3)
  compute
  exact (B1 B2 B3)


order.list_prf3_6 = proof
  compute
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro H
  exact (absurd H)


order.list_prf3_7 = proof
  compute
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  trivial




order.list_prf3_4 = proof
  compute
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  intro
  trivial


order.list_prf2_4 = proof
  intro a,con,cla,x,xs,y,ys
  compute
  intro E
  intro T1,T2,T3,T4,T5,T6
  intro H1
  intro I1
  intro I2
  rewrite sym (eq_symm x y I1)
  compute
  exact (H1 I2)


order.list_prf2_3 = proof
  intro
  intro
  intro
  intro
  intro
  intro H
  exact (absurd H)


order.list_prf2_2 = proof
  intro
  intro
  intro
  intro
  intro
  intro E
  exact (absurd E)


order.list_prf2_1 = proof
  intro
  intro
  intro
  intro
  trivial


order.list_prf1_2 = proof
  intro a,con,cla,x,xs,A,B
  intro H
  rewrite sym (eq_refl x)
  compute
  exact H


