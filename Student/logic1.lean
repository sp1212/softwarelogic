def isEven (n : Nat) : Prop := n % 2 = 0

-- predicates are functions that return paramaterized propositions

#check isEven 0
#check isEven 1

#reduce isEven 0
#reduce isEven 1
#reduce isEven 2
#reduce isEven 3

-- a predicate represents a property of the object to which it pertains

def zornz : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
λ n => match n with
| 0 => (Or.inl rfl) -- rfl is the same as (Eq.refl 0) where the 0 is inferred
| (_ + 1) => Or.inr (λ h => nomatch h)

#reduce zornz 3

#reduce isEven 0 -- returns a proposition that 0 = 0, there is a proof of this
#reduce isEven 1 -- returns a proposition that 1 = 0, there is not a proof of this

variable
  (P : Type)
  (Q : P → Prop)
  (R : Prop)
  (t : P)

#check P
#check Q

#check Q t
#check ∀ (p : P), Q p -- "every p has the property Q"

#check ∀ (x : P), R

-- general form
example : ∃ (p : P), Q p := _

-- introduction
def exists_even_nat : ∃ (n : Nat), isEven n := ⟨ 2, rfl ⟩

--elimination rule
def foo : (∃ (n : Nat), isEven n) → True
| ⟨ n', pf ⟩ => _

example : ∃ (n : Nat), n ≠ 0 := ⟨ 5, _ ⟩

#check 1 = 0
#check Eq 1 0

#check Eq.refl 1

-- Lean reduces expressions
example : 1 + 1 = 2 := rfl

-- can't be proven
example : 1 = 2 := Eq.refl 2

inductive IsEven : Nat → Prop
| zero_is_even : IsEven 0 -- giving a name to an assumed proof that zero is even
| even_plus_2_even : ∀ (n : Nat), IsEven n → IsEven (n + 2)

open IsEven
example : IsEven 0 := zero_is_even
example : IsEven 4 := even_plus_2_even 2 _
