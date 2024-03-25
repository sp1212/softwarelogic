#reduce Nat.succ <$> [0,1,2]

#check Functor
/-!
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
-/

inductive Box (α : Type)
| contents (a : α)

def box_map {α β : Type} : (α → β) → Box α → Box β
| f, (Box.contents a) => Box.contents (f a)

instance : Functor Box := ⟨ box_map, _ ⟩

#reduce Nat.succ <$> (Box.contents 2)
