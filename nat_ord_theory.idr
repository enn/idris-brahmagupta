module nat_ord_theory

nat_compare : Nat -> Nat -> Ordering
nat_compare = compare

ord_eq_refl_Nat : (x : Nat) -> nat_compare x x = EQ
ord_eq_refl_Nat = ?p1

ord_eq_symm_Nat : (x : Nat) -> (y : Nat) -> nat_compare x y = EQ -> nat_compare y x = EQ
ord_eq_symm_Nat = ?p2

ord_eq_trans_Nat : (x : Nat) -> (y : Nat) -> (z : Nat) -> nat_compare x y = EQ -> nat_compare y z = EQ -> nat_compare x z = EQ
ord_eq_trans_Nat = ?p3

instance Uninhabited (LT = EQ) where { uninhabited refl impossible }
instance Uninhabited (GT = EQ) where { uninhabited refl impossible }
instance Uninhabited (EQ = LT) where { uninhabited refl impossible }
instance Uninhabited (EQ = GT) where { uninhabited refl impossible }
instance Uninhabited (Prelude.Classes.LT = GT) where { uninhabited refl impossible }
instance Uninhabited (Prelude.Classes.GT = LT) where { uninhabited refl impossible }

ord_trans_Nat : (x : Nat) -> (y : Nat) -> (z : Nat) -> nat_compare x y = LT -> nat_compare y z = LT -> nat_compare x z = LT
ord_trans_Nat = ?p4

ord_symm_Nat : (x : Nat) -> (y : Nat) -> nat_compare x y = LT -> nat_compare y x = GT
ord_symm_Nat = ?p5

ord_trans_Nat' : (x : Nat) -> (y : Nat) -> (z : Nat) -> nat_compare x y = GT -> nat_compare y z = GT -> nat_compare x z = GT
ord_trans_Nat' = ?p6

ord_symm_Nat' : (x : Nat) -> (y : Nat) -> nat_compare x y = GT -> nat_compare y x = LT
ord_symm_Nat' = ?p7

---------- Proofs ----------

nat_ord_theory.p3 = proof
  intro x
  induction x
  compute
  intro y
  intro z
  case z
  compute
  intros
  trivial
  compute
  case y
  compute
  intros
  trivial
  compute
  intro n2,n1,E,H
  trivial
  compute
  intro H,H2,y
  case y
  compute
  intro z,X
  exact (absurd X)
  intro n3
  intro z
  case z
  compute
  intros
  trivial
  compute
  intro n4
  intro E
  intro E2
  exact (H2 n3 n4 E E2)


nat_ord_theory.p2 = proof
  intro x
  induction x
  intro y
  case y
  compute
  intro
  trivial
  compute
  intro
  intro e
  exact (absurd e)
  intro z,H,y
  case y
  compute
  intro E
  exact (absurd E)
  compute
  intro n2,H2
  exact (H n2 H2)


nat_ord_theory.p7 = proof
  intro x
  induction x
  compute
  intro y
  case y
  compute
  intro E
  exact (absurd E)
  compute
  intro z,E
  exact (absurd E)
  compute
  intro n0,H,y
  case y
  compute
  intros
  trivial
  compute
  intro n1,H1
  exact (H n1 H1)


nat_ord_theory.p6 = proof
  intro x
  induction x
  compute
  intro y
  case y
  compute
  intro z,E
  exact (absurd E)
  compute
  intro n1,z
  intro E
  exact (absurd E)
  compute
  intro n0,H,y
  case y
  compute
  intro z
  case z
  compute
  intros
  trivial
  compute
  intro n2
  intro 
  intro E
  exact (absurd E)
  compute
  intro n1,z
  case z
  compute
  intros
  trivial
  compute
  intro n2,H1
  intro H2
  exact (H n1 n2 H1 H2)


nat_ord_theory.p5 = proof
  intro x
  induction x
  compute
  intro y
  case y
  compute
  intro E
  exact (absurd E)
  compute
  intros
  trivial
  compute
  intro n0,H,y
  case y
  compute
  intro E
  exact (absurd E)
  compute
  intro n2,H2
  exact (H n2 H2)


nat_ord_theory.p4 = proof
  intro x
  induction x
  intro y
  case y
  compute
  intro 
  intro E
  exact (absurd E)
  compute
  intro n1
  intro z
  intro E
  case z
  compute
  intro E'
  exact (absurd E')
  compute
  intro n2,E2
  trivial
  compute
  intro n0
  intro H
  intro y
  case y
  compute
  intro z,E
  exact (absurd E)
  intro n1
  compute
  intro z,H1
  case z
  compute
  intro E
  trivial
  compute
  intro n2
  intro H3
  exact (H n1 n2 H1 H3)




nat_ord_theory.p1 = proof
  intro x
  induction x
  compute
  trivial
  compute
  intro
  intro
  trivial


