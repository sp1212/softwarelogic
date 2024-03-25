/-!
truth table for P implies Q
P → Q

P     Q     P → Q
true  true  true
false false true
true  false false
false true  true

counterintuitive for false true true
-/

#check Empty

def e2e : Empty → Empty
| e => e

def n2e : Nat → Empty
| n => _
