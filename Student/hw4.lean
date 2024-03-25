/-!
Reduce a list of strings to a Boolean, true if all strings in the list are of even length
-/

def isEvenLen : String → Bool := λ s => s.length % 2 == 0

#eval isEvenLen "Eveneven"
#eval isEvenLen "Odd"

-- "analog of addition"
def combine : String → Bool → Bool
| s, b => (isEvenLen s) && b

#eval combine "even" True
#eval combine "even" False
#eval combine "odd" True
#eval combine "odd" False

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

def el := ["even", "eveneven", "moreeven", "ev", "eeeeee"]
def ol := ["odd", "moreodd", "odder"]
def both := ["even", "odd"]
def both2 := ["odd", "even"]
def numlist := [1,2,3,4,5]

#eval foldr combine True []
#eval foldr combine True el
#eval foldr combine True ol
#eval foldr combine True both
#eval foldr combine True both2
#eval foldr Nat.add 0 numlist
#eval foldr Nat.mul 1 numlist
#eval foldr String.append "" both

/-!
What can go wrong?
You can pass a non-identity element

What rules must be enforced?
- id is the identity element for op
- op must be associative

How can we be assured that the rules are enforced?

-/

inductive my_monoid' (α : Type) where
| mk : (op : α → α → α) →
(id : α) →
(left_id : ∀ (a : α), op id a = a) →
(right_id : ∀ (a : α), op a id = a) → my_monoid' α

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a)
(right_id : ∀ (a : α), op a id = a)

-- .mk is default constructor
def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check my_monoid
#check a_monoid.op
