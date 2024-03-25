inductive BobStudiesAtUVA
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVA
| attendsClasses
| paidTuition

inductive MarkoStudiesAtUVA

def neg (α : Type) := α → Empty

example : neg MarkoStudiesAtUVA :=
λ m : MarkoStudiesAtUVA => nomatch m

inductive BobStudiesAtUVAAndMaryStudiesAtUVA
| and (b : BobStudiesAtUVA) (m : MaryStudiesAtUVA)

def b : BobStudiesAtUVA := BobStudiesAtUVA.paidTuition
def m : MaryStudiesAtUVA := MaryStudiesAtUVA.paidTuition

example : BobStudiesAtUVAAndMaryStudiesAtUVA :=
  BobStudiesAtUVAAndMaryStudiesAtUVA.and b m

inductive BobStudiesAtUVAOrMaryStudiesAtUVA
| left (b : BobStudiesAtUVA)
| right (m : MaryStudiesAtUVA)

example : BobStudiesAtUVAOrMaryStudiesAtUVA :=
  BobStudiesAtUVAOrMaryStudiesAtUVA.left b

inductive MyAnd (α β : Type) : Type
| mk (a : α) (b : β)

inductive MyOr (a β : Type) : Type
| inl (a : α)
| inr (b : β)

example : MyAnd BobStudiesAtUVA MaryStudiesAtUVA := MyAnd.mk b m

example : MyOr BobStudiesAtUVA MaryStudiesAtUVA := MyOr.inl b -- not sure what's wrong here
example : MyOr BobStudiesAtUVA MaryStudiesAtUVA := MyOr.inr m

def MyNot (α : Type) := α → Empty

example : MyNot BobStudiesAtUVA := λ b => _ -- Nope
example : MyNot MarkoStudiesAtUVA := λ m => nomatch m


#check (1, "Hello")

example : Prod BobStudiesAtUVA MaryStudiesAtUVA := Prod.mk b m
example : BobStudiesAtUVA × MaryStudiesAtUVA := (b, m)
example : BobStudiesAtUVA × MaryStudiesAtUVA := (b, m)

example : BobStudiesAtUVA × MaryStudiesAtUVA → BobStudiesAtUVA := λ p => p.fst
example : BobStudiesAtUVA × MaryStudiesAtUVA → MaryStudiesAtUVA := λ p => p.2

example : Sum BobStudiesAtUVA MarkoStudiesAtUVA := Sum.inl b -- b is a proof of left
example : BobStudiesAtUVA ⊕ MarkoStudiesAtUVA := Sum.inr _ -- no proof, uninhabited type

example : BobStudiesAtUVA ⊕ MarkoStudiesAtUVA → BobStudiesAtUVA
| (Sum.inl l) => l
| (Sum.inr r) => nomatch r

example : neg MarkoStudiesAtUVA := λ p : MarkoStudiesAtUVA => nomatch p

example : neg (MaryStudiesAtUVA × MarkoStudiesAtUVA) := λ p => nomatch (p.2)


-- Proof Irrelevance
inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop

-- intro
example : And B M := And.intro B.paid M.classes
def b_and_m_true : And B M := And.intro B.paid M.classes
theorem b_and_m_true' : And B M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes ⟩

-- elim
example : B ∧ M → M := λ bm => bm.right
example : B ∧ M → M := λ bm => bm.2
example : B ∧ M → B := fun bm => bm.1

-- intro
example : B ∨ K := Or.inl B.paid

def foo : B ∧ Not K := ⟨ B.paid, λ K => nomatch K ⟩
example : B ∧ ¬K := foo

example : B ∨ K := Or.inl B.paid

example : B ∨ K → B := λ bork => match bork with
| Or.inl b => b
| Or.inr k => nomatch k

example :
  ∀ (Raining Sprinkling Wet : Prop),
  (Raining ∨ Sprinkling) →
  (Raining → Wet) →
  (Sprinkling → Wet) →
  Wet :=
  λ _ _ _ rors rw sp =>
  match rors with
| Or.inl r => rw r
| Or.inr s => sp s

-- intro example
def notK : ¬K := λ k => nomatch k

-- elim example (law of no contradiction example)
example (P : Prop) : ¬P → P → False := λ np p => np p

example (P : Prop) : ¬¬P → P
| nnp => _ -- we're stuck!

-- law of the excluded middle (?)
example (P : Prop) : (P ∨ ¬P) → (¬¬P → P)
| pornp => match pornp with
  | Or.inl p => λ _ => p
  | Or.inr np => λ nnp => nomatch (nnp np)

--- ∀ (P : Prop), P ∨ ¬P

-- Implication (P → Q)
-- intro: show that from and assumed proof of P, you can derive a proof of Q
-- elim: apply that function to proof of P to get a proof of Q
-------------------------------------------------------------------------------------------

-- all four examples below are equivalent
example (P Q : Prop) : P ∧ Q → Q ∧ P := λ (h : P ∧ Q) => And.intro h.2 h.1
example (P Q : Prop) : P ∧ Q → Q ∧ P := λ (h : P ∧ Q) => ⟨ h.2, h.1 ⟩
example (P Q : Prop) : P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p
example (P Q : Prop) : P ∧ Q → Q ∧ P
| ⟨ p, q ⟩ => ⟨ q, p ⟩


example (P Q : Prop) : P ∧ Q → P ∨ Q
| ⟨ p, _ ⟩ => Or.inl p

example (P Q : Prop) : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q

/-
Proof by contradiction
to prove P,
assume ¬P
show ¬P → False
¬¬P → P
-/

example : ∀ (P : Prop), ¬¬ P → P := λ P nnp => _

#check Classical.em

example (P : Prop) : (¬¬P → P) :=
match (Classical.em P) with
  | Or.inl p => λ _ => p
  | Or.inr np => λ _ => by contradiction

def one_not_eq_zero (n : Nat) : n = 1 → n ≠ 0 :=
λ (neq1 : n = 1) => λ neq0 => by

  rw [neq1] at neq0
  cases neq0

/-
def one_not_eq_zero (n : Nat): n = 1 → n ≠ 0 :=
λ h => match n with
| Nat.zero => nomatch h
| Nat.succ n' => λ k => by
  rw [k] at h
  cases h
-/

#check 1 = 0
#check Eq 1 0
#check Eq.refl 1

example : 1 = 1 := Eq.refl 1
