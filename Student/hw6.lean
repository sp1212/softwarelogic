/-!
We've seen that we can generalize the notion of
mapping objects of one container-like type to
objects of a correspond value of the same type
by replacing each *element* in one container
corresponding objects computed by applying an
element-wise conversion function to each object
in the input container. Here we give two examples
that we saw in class: functions for mapping over
Lists, and functions for mapping over Options.
-/

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-!
We now present two more "container-like" types that
we saw in class. The Box type is a container type for
exactly one object some type, α, and Tree is such a
type for representing binary trees of such objects.
-/
inductive Box (α : Type)
| contents (a : α)

def box_containing_zero := Box.contents Nat.zero
#reduce box_containing_zero

inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

/-! Problem #1
Define box_map and tree_map functions and
use #eval to give examples of applying these
functions to a few arguments.
-/

def box_map {α β : Type} : (α → β) → Box α → Box β
| f, Box.contents a => Box.contents (f a)

#reduce box_map Nat.succ box_containing_zero

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

/-!
The functor type, below, generalizes the idea
that we can map over *any* polymorphic container
type. The functor type takes a polymorphic type
(builder), such as List or Option, and augments
it with a map function for objects of that type.
Here we don't try to specify rules for functors.
We'll see them shortly. For now the definition
follows has everything we need.
-/

-- c is a polymorphic container
structure functor'' (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

class functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

-- can also define with the class keyword

/-!
Here are functor *instances* for the polymorphic
container-like List and Option types.
-/

def list_functor : functor'' List  := functor''.mk list_map
def option_functor : functor'' Option  := functor''.mk option_map

instance : functor List := ⟨ list_map ⟩
instance : functor Box := ⟨ box_map ⟩
instance : functor Option := ⟨ option_map ⟩

/-! Problem #2

Complete the definition of a polymorphic do_map
function. Note that this function, map, is not
the same as the functor field value, functor.map.
Hint: See the "convert" function from class.
-/

def do_map {α β : Type} {c : Type → Type} (m : functor'' c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

def do_map' {α β : Type} {c : Type → Type} [m : functor c] :
  (f : α → β) → c α → c β
| f, c => m.map f c

-- These test cases should succeed when do_map is right
#eval do_map list_functor Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map option_functor (λ s => s ++ "!") (some "Hi")

#reduce do_map' Nat.succ [1,2,3]


/-! Problem #3

Briefly explain why you can't apply map to a value of type
(Tree Nat) at this point.

Here:
We need to define the appropriate functor(s) before we can apply the mapping function
given how we have setup the data types.
-/

/-! Problem #4

Define functor instances for Box and Tree.
-/
def box_functor : functor'' Box  := functor''.mk box_map
def tree_functor : functor'' Tree  := functor''.mk tree_map


/-! Problem #5

Give working examples, using #eval, of applying do_map
to a Box Nat and Tree String values.
-/
#reduce do_map box_functor Nat.succ box_containing_zero
#reduce do_map tree_functor Nat.succ a_tree

/-!
Here's an infix notation for do_map and a few examples
of its use.
-/

infix:50 "<$>"  => do_map
#eval Nat.succ <$> [1,2,3]
#eval (λ s => s ++ "!") <$> ["Hi", "Yo"]

#eval Nat.succ <$> [1,2,3]
#eval do_map list_functor Nat.succ [1,2,3]  -- [2, 3, 4]

#eval (λ s => s ++ "!") <$> ["Hi", "Yo"]
#eval do_map option_functor (λ s => s ++ "!") (some "Hi")

/-! Problem #6

Rewrite your/our examples of mapping over List,
Option, Box, and Tree values using <$> notation.
-/

#eval Nat.succ <$> box_containing_zero
#eval Nat.succ <$> a_tree
#eval (λ s => s ++ "!") <$> (some "Hi")
