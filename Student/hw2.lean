def add : (a b : Nat) → Nat
| a, Nat.zero => a
| a, Nat.succ n' => add (Nat.succ a) n'

#reduce add 2 1
#reduce add 0 0
#reduce add 0 4
#reduce add 8 4
#reduce add 8 0


def appendbackwards {T : Type} : (n m : List T) → List T
| n, List.nil => n
| n, List.cons m n' => appendbackwards (List.cons m n) n'

def append {T : Type} : (n m : List T) → List T
| List.nil, m => m
| List.cons h n', m => List.cons h (append n' m)

def e : List Nat := List.nil
def l1 : List Nat := List.cons 1 e
#reduce e
#reduce l1
def l2 : List Nat := List.cons 0 l1
#reduce l2

#reduce appendbackwards l2 l1
#reduce append l2 l1

def mul : Nat → Nat → Nat
| _, 0 => 0
| n, (m' + 1) => add n (mul n m')

#eval mul 5 4
#eval mul 6 0
#eval mul 12 12

def exp : Nat → Nat → Nat
| _, 0 => 1
| n, (m' + 1) => mul n (exp n m')

#eval exp 2 4
#eval exp 8 0
#eval exp 25 2
