structure my_monoid' (α : Type) where
(op : α → α → α)
(id : α)

def foldr' {α : Type} : my_monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)

#eval foldr' (my_monoid'.mk Nat.add 0) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk String.append "") ["Hello, ", "World", "!"]

def nary_add := foldr' (my_monoid'.mk Nat.add 0)
#eval nary_add [1,2,3,4,5]

def nary_mul := foldr' (my_monoid'.mk Nat.mul 1)
#eval nary_mul [1,2,3,4,5]

def nary_append := foldr' (my_monoid'.mk String.append "")
#eval nary_append ["Hello", "Higher", "Mathematics"]

/-!
What does a monoid do?

It extends a binary operator to be a n-ary operator
-/

structure my_monoid (α : Type) where
(op : α → α → α)
(id : α)
(left_id : ∀ a, op id a = a)
(right_id : op a id = a)
(op_assoc : ∀ a b c, op a (op b c) = op (op a b) c)

def foldr {α : Type} : my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr nat_add_monoid [1,2,3,4,5]

def nat_add_monoid' : my_monoid Nat :=
⟨ Nat.add,
  0,
  λ a => by simp (Nat.add),
  λ a => by simp (Nat.add),
  sorry
⟩

def nat_mul_monoid'' : my_monoid Nat :=
⟨ Nat.mul,
  1,
  λ a => by simp (Nat.mul),
  λ a => by simp (Nat.mul),
  sorry
⟩

def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)
#eval nary_mul' [1,2,3,4,5]

#check (@Option)

def pred : Nat → Option Nat
| Nat.zero => Option.none
| (Nat.succ n') => n'

#reduce pred 3
#reduce pred 0

def option_map {α β : Type} : (α → β) → Option α → Option β
| f, Option.none => Option.none
| f, Option.some a => Option.some (f a)


-- creating a tree data type, two different ways to write the constructor with one commented out
inductive Tree (α : Type) : Type
| empty
--| node : α → Tree α → Tree α → Tree α
| node (a : α) (l r : Tree α) : Tree α

structure functor {α β : Type} (c : Type → Type) : Type where
map (f : α → β) (ic : c α) : c β

--def list_functor {α β : Type} : @functor α β List := functor.mk list_map
def option_functor {α β : Type} : @functor α β Option := functor.mk option_map

def convert {α β : Type} (c : Type → Type) (m : @functor α β c) : (f : α → β) → c α → c β
| f, c => m.map f c

#reduce convert Option option_functor Nat.succ (Option.some 4)

inductive box {α : Type}
| contents (a : α)

def tree_map {α β : Type} : (α → β) → Tree α → Tree β
| _, Tree.empty => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

def a_tree :=
  Tree.node
    1
    (Tree.node
    2
    Tree.empty
    Tree.empty
    )
    (Tree.node
    3
    Tree.empty
    Tree.empty
    )

#reduce tree_map Nat.succ a_tree
