/-!
#1

Define a function, dec' : Nat → Nat, that takes any Nat, n, and that
returns 0 if n is 0 and that otherwise returns one less than n. Hint:
case analysis on n. When you've succeeded the following test cases
should run and return the expected values.
-/

def dec' : Nat → Nat
| Nat.zero => Nat.zero
| Nat.succ n' => n'

#eval dec' 2    -- expect 1
#eval dec' 1    -- expect 0
#eval dec' 0    -- expect 0

def dec2 : Nat → Nat
| 0 => 0
| 1 => 0
| Nat.succ (Nat.succ n'') => n''

#eval dec2 0
#eval dec2 1
#eval dec2 2
#eval dec2 3

/-
#2

Define a function, l2l, polymorphic in two type parameters, α and β, that
also takes a function, f, from α to β and a list of α values and that returns
a  list of corresponding β values. As an example, (l2l Nat.succ [0, 1, 2]) is
expected to return [1, 2, 3]. Write a few test cases where α is String, β is
Nat, and f is String.length. Hint: Use case analysis on the incoming list: it
will be either List.nil or (List.cons h t), the latter of which can also be
written as (h::t).
-/

def l2l {α β : Type} : (α → β) → List α → List β
| _, List.nil => List.nil
| f, List.cons h t => List.cons (f h) (l2l f t)

#eval l2l Nat.succ [0, 1, 2]
#eval l2l Nat.succ [2, 8, 12]
#eval l2l String.length ["four", "words"]
#eval l2l String.length []

/-!
#3

Define a data type, called PFRV (short for "partial function return value"),
polymorphic in one type, α, where a value of this type is either "undefined"
or "defined α". If α is Nat, for example, then you would have (undefined) and
(defined 3) as values of this type. In the case of undefined, you will have
to disable implicit arguments, as there's no value provided to this constructor
from which Lean can infer α.
-/

-- similar to Option or Maybe in some functional languages

inductive PFRV (α : Type)
| undefined
| defined (a : α)

#check @PFRV.undefined Nat    -- expect PFRV
#check PFRV.defined 3         -- Expect PFRV

def p1 : PFRV Nat := PFRV.undefined
def p2 := PFRV.defined 1

#check p1
#check p2

/-!
#4

Define a variant of dec', called dec, that takes a natural number, n, as an
argument and that returns a (PFRV Nat). This value must be "PFRV.undefined"
if n = 0, reflecting the idea that dec is a partial function, one that is not
defined for the argument value, 0; and that returns one less than n otherwise.
You will thus represent a partial function from Nat to Nat as a total function
from Nat to PFRV Nat.
-/

def dec : Nat → PFRV Nat
| Nat.zero => PFRV.undefined
| Nat.succ n' => PFRV.defined n'

#reduce dec 2

/-!
#5

Define a function, isZero from Nat to Bool that returns true if its argument
is zero and false otherwise. Write a few test cases to show that it works.
-/

def isZero : Nat → Bool
| Nat.zero => True
| _ => False

#eval isZero 9845
#eval isZero 0
#eval isZero 92

/-!
#6

Define a function, isDef, from PFRV α to Bool, that returns false if the given
PFRV α is "undefined" and true otherwise. The following test cases should then
return the expected values.
-/

def isDef : PFRV α → Bool
| PFRV.undefined => False
| _ => True

#eval isDef (dec 0)   -- expect false
#eval isDef (dec 1)   -- expect true

/-!
New Material
-/

/-!
The fold right function
-/
-- version 1: add up numbers in list

def foldr''' : (Nat → Nat → Nat) → Nat → List Nat → Nat
| _, id, List.nil => id
| op, id, h::t => op h (foldr''' op id t)

#reduce foldr''' Nat.add 0 [1,2,3,4,5]
#reduce foldr''' Nat.mul 1 [1,2,3,4,5]

#reduce foldr''' Nat.sub 0 [5,3,1] -- essentially 5-(3-1)

/-!
fold_str that takes a list of strings and returns a single string
in which all the given srings are appended using String.append
-/

def fold_str : (String → String → String) → String → List String → String
| _, id, [] => id
| op, id, h::t => op h (fold_str op id t)

#eval fold_str String.append "" ["Hello","World","List","of","Strings"]

def foldr' {α : Type} : (α → α → α) → α → List α → α
| _, id, [] => id
| op, id, h::t => op h (foldr' op id t)

#eval foldr' String.append "" ["Hello","World","List","of","Strings"]
