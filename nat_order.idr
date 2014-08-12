module nat_order

import order

instance SpecifiedOrdering Nat where
 compare' = compare
 
 eq_refl = ?p1
 eq_symm = ?p2
 eq_trans = ?p3
 
 -- ordering relation
 ord_lt_gt = ?p4
 ord_gt_lt = ?p5
 ord_lt_eq = ?p6
 ord_gt_eq = ?p7
 ord_lt_trans = ?p8


---------- Proofs ----------

nat_order.p2 = proof
  intro x
  induction x
  intro y
  case y
  compute
  intro H
  exact H
  intro n1
  compute
  intro H
  exact (absurd H)
  intro n0,IH,y
  case y
  compute
  intro H
  exact (absurd H)
  intro n1
  compute
  exact (IH n1)


nat_order.p8 = proof
  intro x
  induction x
  intro y
  case y
  intro z
  case z
  compute
  intros
  trivial
  intro n2
  compute
  intros
  trivial
  intro n1,z
  compute
  case z
  compute
  intro H,H'
  exact (absurd H')
  intro n2
  compute
  intros
  trivial
  intro n0,IH,y,z
  case y
  case z
  compute
  intro H
  exact (absurd H)
  intro n2
  compute
  intro H
  exact (absurd H)
  intro n1
  case z
  compute
  intro H,H'
  trivial
  intro n2
  compute
  intro H1,H2
  exact (IH _ _ H1 H2)


nat_order.p7 = proof
  intro x
  induction x
  intro y
  case y
  intro z
  case z
  compute
  intros
  trivial
  intro n2
  compute
  intro E,H
  exact (absurd H)
  compute
  intro n1,z,H
  exact (absurd H)
  intro n0,IH,y,z
  compute
  case y
  compute
  case z
  compute
  intros
  trivial
  compute
  intro n2,H'
  intro H''
  exact (absurd H'')
  intro n1
  case z
  compute
  intro H1,H2
  exact (absurd H2)
  intro n2
  compute
  intro H1,H2
  exact (IH _ _ H1 H2)


nat_order.p6 = proof
  intro x
  induction x
  intro y
  case y
  intro z
  case z
  compute
  intros
  trivial
  intro n2
  compute
  intros
  trivial
  intro n1,z
  case z
  compute
  intro E,H
  exact (absurd H)
  intro n2
  compute
  intros
  trivial
  intro n0,H
  intro y,z
  compute
  case y
  compute
  intro H'
  exact (absurd H')
  intro n1
  case z
  compute
  intro H1,H2
  exact (absurd H2)
  compute
  intro n2
  intro H1,H2
  exact (H _ _ H1 H2)


nat_order.p5 = proof
  intro x
  induction x
  intro y
  case y
  compute
  intro H
  exact (absurd H)
  intro n1
  compute
  intro H
  exact (absurd H)
  intro n0
  intro IH
  intro y
  case y
  compute
  intros
  trivial
  intro n1
  compute
  intro H
  exact (IH _ H)


nat_order.p4 = proof
  intro x
  induction x
  intro y
  case y
  compute
  intro H
  exact (absurd H)
  intro n1
  compute
  intros
  trivial
  intro n0
  intro IH
  intro y
  case y
  compute
  intro H
  exact (absurd H)
  intro n1
  compute
  intro H
  exact (IH _ H)


nat_order.p3 = proof
  intro x
  induction x
  intro y
  case y
  intro z
  case z
  compute
  intros
  trivial
  compute
  intros
  trivial
  compute
  intro n1,z,H
  exact (absurd H)
  compute
  intro n0,IH
  intro y
  case y
  compute
  intro z,H
  exact (absurd H)
  intro n1,z
  case z
  compute
  intros
  trivial
  compute
  intro n3,H1,H2
  exact (IH _ _ H1 H2)



nat_order.p1 = proof
  intro x
  induction x
  compute
  trivial
  intro x'
  compute
  intro
  trivial


