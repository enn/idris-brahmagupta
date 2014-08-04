module sums

%default total

%elim data E : Nat -> Type where
 V : Fin n -> E n
 A : E n -> E n -> E n
 M : E n -> E n -> E n

eE : Vect n Nat -> E n -> Nat
eE env (V i) = index i env
eE env (A p q) = eE env p + eE env q
eE env (M p q) = eE env p * eE env q

Sum : Type -> Type
Sum = List

Product : Type -> Type
Product = List

eP : Vect n Nat -> Product (Fin n) -> Nat
eP env [] = 1
eP env (x :: xs) = index x env * eP env xs

eP_lemma1 : (env : Vect n Nat) -> (p : Product (Fin n)) -> (q : Product (Fin n)) ->
             eP env (p ++ q) = eP env p * eP env q
eP_lemma1 = ?eP_lemma1_proof

eSP : Vect n Nat -> Sum (Product (Fin n)) -> Nat
eSP env [] = 0
eSP env (x :: xs) = eP env x + eSP env xs

eSP_lemma1 : (env : Vect n Nat) -> (p : Sum (Product (Fin n))) -> (q : Sum (Product (Fin n))) ->
             eSP env (p ++ q) = eSP env p + eSP env q
eSP_lemma1 = ?eSP_lemma1_proof

multiply_by : Product (Fin n) -> Sum (Product (Fin n)) -> Sum (Product (Fin n))
multiply_by p [] = []
multiply_by p (x :: xs) = (p ++ x) :: multiply_by p xs

multiply_by_lemma1 : (n : Nat) -> (q : Sum (Product (Fin n))) -> multiply_by [] q = q
multiply_by_lemma1 = ?multiply_by_lemma1_proof

multiply_by_spec : (env : Vect n Nat) ->
                   (p : Product (Fin n)) -> (q : Sum (Product (Fin n))) ->
                   eP env p * eSP env q = eSP env (multiply_by p q)
multiply_by_spec = ?multiply_by_spec_proof

multiply : Sum (Product (Fin n)) -> Sum (Product (Fin n)) -> Sum (Product (Fin n))
multiply [] q = []
multiply (x :: xs) q = multiply_by x q ++ multiply xs q

multiply_spec : (env : Vect n Nat) ->
                (p : Sum (Product (Fin n))) -> (q : Sum (Product (Fin n))) ->
                eSP env p * eSP env q = eSP env (multiply p q)
multiply_spec = ?multiply_spec_proof

multiply_out : E n -> Sum (Product (Fin n))
multiply_out (V i) = [[i]]
multiply_out (A p q) = multiply_out p ++ multiply_out q
multiply_out (M p q) = multiply (multiply_out p) (multiply_out q)

multiply_out_correct : (env : Vect n Nat) -> (e : E n) ->
                       eE env e = eSP env (multiply_out e)
multiply_out_correct = ?multiply_out_correct_proof

---------- Proofs ----------

sums.multiply_out_correct_proof = proof
  intros
  induction e
  compute
  intro
  rewrite sym (multOneRightNeutral (index f__0 env))
  rewrite sym (plusZeroRightNeutral (index f__0 env))
  exact refl
  intros
  compute
  rewrite sym (eSP_lemma1 env (multiply_out e__0) (multiply_out e__2))
  rewrite sym ihe__0
  rewrite sym ihe__2
  exact refl
  compute
  intros
  rewrite sym (multiply_spec env (multiply_out e__3) (multiply_out e__4))
  rewrite (multiply_spec env (multiply_out e__3) (multiply_out e__4))
  rewrite ihe__3
  rewrite ihe__4
  exact refl


sums.multiply_spec_proof = proof
  intros
  induction p
  compute
  exact refl
  compute
  intros
  rewrite sym ihl__0
  rewrite ihl__0
  rewrite (eSP_lemma1 env (multiply_by t__0 q) (multiply l__0 q))
  rewrite (eSP_lemma1 env (multiply_by t__0 q) (multiply l__0 q))
  rewrite sym (eSP_lemma1 env (multiply_by t__0 q) (multiply l__0 q))
  rewrite sym (multiply_by_spec env t__0 q)
  rewrite (multiply_by_spec env t__0 q)
  rewrite ihl__0
  rewrite (multDistributesOverPlusLeft (eP env t__0) (eSP env l__0) (eSP env q))
  exact refl


sums.eSP_lemma1_proof = proof
  intros
  induction p
  compute
  exact refl
  compute
  intro
  intros
  rewrite sym ihl__0
  rewrite sym (plusAssociative (eP env t__0) (eSP env l__0) (eSP env q))
  exact refl


sums.eP_lemma1_proof = proof
  intros
  induction p
  compute
  rewrite sym (plusZeroRightNeutral (eP env q))
  exact refl
  compute
  intros
  rewrite ihl__0
  rewrite sym ihl__0
  rewrite sym (multAssociative (index t__0 env) (eP env l__0) (eP env q))
  exact refl


sums.multiply_by_spec_proof = proof
  intros
  induction q
  compute
  rewrite sym (multZeroRightZero (eP env p))
  exact refl
  compute
  intros
  rewrite sym ihl__0
  rewrite sym ihl__0
  rewrite  ihl__0
  rewrite sym (multDistributesOverPlusRight (eP env p) (eP env t__0) (eSP env l__0))
  rewrite (eP_lemma1 env p t__0)
  rewrite sym (eP_lemma1 env p t__0)
  exact refl


sums.multiply_by_lemma1_proof = proof
  intro n
  intro q
  induction q
  compute
  exact refl
  compute
  intros
  rewrite ihl__0
  exact refl

