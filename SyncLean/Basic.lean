import Std.Tactic.BVDecide

def inputsToSel (i: Nat): Nat := -- i.log2
  match i with
  | 0 => 0
  | n + 1 => 1 + n.log2

#eval (inputsToSel 0) -- 1
#eval (inputsToSel 1) -- 1
#eval (inputsToSel 2) -- 1
#eval (inputsToSel 3) -- 2
#eval (inputsToSel 4) -- 3
#eval (inputsToSel 5) -- 3
#eval (inputsToSel 6) -- 3
#eval (inputsToSel 7) -- 3
#eval (inputsToSel 8) -- 3
#eval (inputsToSel 9) -- 4

def mux {w i}
  (inputs: Vector (BitVec w) i)
  (sel: BitVec (inputsToSel i))
  (p: sel.toNat < i := by decide +native)
  : BitVec w :=
  inputs[sel.toNat]

def a: BitVec 32 := 1
def b: BitVec 32 := 2
def i2 := #v[a, b]
def s1: BitVec (inputsToSel 2) := 1

#eval (inputsToSel i2.size) -- 1 bit needed
#eval (s1) -- 1#1 (BitVec 1)

#eval (mux i2 s1)

def c: BitVec 32 := 3
def i3 := #v[a, b, c]
def s2: BitVec (inputsToSel 3) := 2
#eval (mux i3 s2) -- 3


-- a + b + c_in -> c_out × sum
def full_adder (a b c_in: Bool) : Bool × Bool  :=
  ( a && b || a && c_in || b && c_in,  a ^^ b ^^ c_in)

#eval (full_adder false false false) -- false false
#eval (full_adder false false true ) -- false true
#eval (full_adder false true  false) -- false true
#eval (full_adder false true  true ) -- true  false
#eval (full_adder true  false false) -- false false
#eval (full_adder true  false true ) -- true  false
#eval (full_adder true  true  false) -- true  false
#eval (full_adder true  true  true ) -- true  true

def adder {w} (a b: BitVec w) (c_in : Bool) (i: Nat): Bool × (BitVec w) :=
  match i with
  | 0      => (c_in, 0)
  | j + 1  =>
    let (c, r) := adder a b c_in j
    let (c_out, s) :=  full_adder (a.getLsbD j) (b.getLsbD j) c
    let bv_s : BitVec w := if s then 1 else 0
    (c_out, r ||| bv_s <<< j)

def a_ : BitVec 2 := 3
def b_ : BitVec 2 := 1

#eval (adder a_  b_  false 2) -- 3 + 1     = (true, 0x0#2)
#eval (a_ + b_ )              -- 3 + 1     = 0x0#2

set_option maxRecDepth 1024
theorem adder_32: ∀ (a b: BitVec 16),
    (adder a b false 16).snd = a + b := by
  simp [adder, full_adder]
  bv_decide

#check Std.HashMap

structure Simulator where
  store : Std.HashMap String Nat

structure Resisters where
  components : List (Simulator -> Simulator)

def s: Simulator := { store := Std.HashMap.emptyWithCapacity 10 }
#check s
def ss: Simulator := { store := s.store.insert "pc" 2 }
#eval (ss.store.getD "pc" 0)

def get (id: String) (s : Simulator) : Nat :=
  s.store.getD id 0

#check get

namespace PcPlus4
def next_pc (a : (Simulator -> Nat)) (s: Simulator): Nat :=
  dbg_trace "next_pc"
  (a s) + 4
end PcPlus4

def pc_plus4 := PcPlus4.next_pc (get "pc")

#eval (pc_plus4 ss)

def reg (f: Simulator -> Simulator) (s: Simulator) : Simulator :=
  dbg_trace "reg"
  f s

def pc_reg (s: Simulator) : Simulator :=
  dbg_trace "pc_reg"
  { store:= s.store.insert "pc" (pc_plus4 s) }

#eval (pc_reg ss)







def plus  (a b : (Simulator -> Nat)) (s: Simulator): Nat :=
  (a s) + (b s)




-- class Component (c: Type) where
--   eval : c → Simulator

-- #check Component
-- #print Component

-- structure CompAdder

-- def adder_eval (_c: CompAdder) (_s: Simulator) :=
--   dbg_trace "comp_adder"
--   ()

-- #check adder_eval

-- instance : Component CompAdder where
--   eval := adder_eval

-- #check adder_eval

-- def ca: CompAdder := {}

-- #eval (Component.eval ca s)

-- structure PcPlus4 {w: Nat} where
--   pc_out: (BitVec w) → BitVec w

-- def pc_plus4_eval (w: Nat) (_c: (PcPlus4 w)) (s: Simulator) : Simulator :=
--   dbg_trace "comp_pw_plus4"
--   s

-- instance : Component PcPlus4 where
--   eval :=
