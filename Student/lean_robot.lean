-- modeling a robot that can rotate and face toward any of three points of a triangle
-- states are oriented and rotations are conducted counter-clockwise (against all intuition)
/-
      0

120      240
-/

inductive State
| s0
| s120
| s240

inductive Rotation
| r0
| r120
| r240

open State Rotation

def act : Rotation → State → State
| r0, s => s
| r120, s0 => s120
| r120, s120 => s240
| r120, s240 => s0
| r240, s0 => s240
| r240, s120 => s0
| r240, s240 => s120

def add_rotation : Rotation → Rotation → Rotation
| r0, r => r
| r, r0 => r
| r120, r240 => r0
| r120, r120 => r240
| r240, r120 => r0
| r240, r240 => r120

def sub_state : State → State → Rotation
| s0, s0 => r0
| s0, s120 => r240
| s0, s240 => r120
| s120, s0 => r120
| s120, s120 => r0
| s120, s240 => r240
| s240, s0 => r240
| s240, s120 => r120
| s240, s240 => r0

instance : Add Rotation := ⟨ add_rotation ⟩
#reduce r120 + r120

instance : AddSemigroup Rotation := { }
