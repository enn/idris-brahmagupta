module fin_ord_theory

import nat_ord_theory

fin_compare : Fin n -> Fin n -> Ordering
fin_compare x y = compare (finToNat x) (finToNat y)

ord_eq_refl_Fin : (x : Fin n) -> fin_compare x x = EQ
ord_eq_refl_Fin = ?p1

ord_eq_symm_Fin : (x : Fin n) -> (y : Fin n) -> fin_compare x y = EQ -> fin_compare y x = EQ
ord_eq_symm_Fin = ?p2

ord_eq_trans_Fin : (x : Fin n) -> (y : Fin n) -> (z : Fin n) -> fin_compare x y = EQ -> fin_compare y z = EQ -> fin_compare x z = EQ
ord_eq_trans_Fin = ?p3

ord_trans_Fin : (x : Fin n) -> (y : Fin n) -> (z : Fin n) -> fin_compare x y = LT -> fin_compare y z = LT -> fin_compare x z = LT
ord_trans_Fin = ?p4

ord_symm_Fin : (x : Fin n) -> (y : Fin n) -> fin_compare x y = LT -> fin_compare y x = GT
ord_symm_Fin = ?p5

ord_trans_Fin' : (x : Fin n) -> (y : Fin n) -> (z : Fin n) -> fin_compare x y = GT -> fin_compare y z = GT -> fin_compare x z = GT
ord_trans_Fin' = ?p6

ord_symm_Fin' : (x : Fin n) -> (y : Fin n) -> fin_compare x y = GT -> fin_compare y x = LT
ord_symm_Fin' = ?p7



---------- Proofs ----------

fin_ord_theory.p1 = proof
  intro n,x
  exact (ord_eq_refl_Nat (finToNat x))


fin_ord_theory.p2 = proof
  intro n,x,y
  exact (ord_eq_symm_Nat (finToNat x) (finToNat y))


fin_ord_theory.p3 = proof
  intro n,x,y,z
  exact (ord_eq_trans_Nat (finToNat x) (finToNat y) (finToNat z))


fin_ord_theory.p4 = proof
  intro n,x,y,z
  exact (ord_trans_Nat (finToNat x) (finToNat y) (finToNat z))


fin_ord_theory.p5 = proof
  intro n,x,y
  exact (ord_symm_Nat (finToNat x) (finToNat y))


fin_ord_theory.p6 = proof
  intro n,x,y,z
  exact (ord_trans_Nat' (finToNat x) (finToNat y) (finToNat z))


fin_ord_theory.p7 = proof
  intro n,x,y
  exact (ord_symm_Nat' (finToNat x) (finToNat y))



