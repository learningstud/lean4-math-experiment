-- https://en.wikipedia.org/wiki/Category_(mathematics)#Examples
import Algebra.Basic

/-
class Magma (α : Type u) where
  op : α → α → α
-- Later instances override previous ones
instance : Magma Nat where op := Nat.mul
#eval (Magma.op : Nat → Nat → Nat) 1 2 -- 2
instance : Magma Nat where op := Nat.add
#eval (Magma.op : Nat → Nat → Nat) 1 2 -- 1
-/

structure Mag where
  carrier : Type u
  op : carrier → carrier → carrier
instance : CoeSort Mag (Type u) where coe M := M.carrier
-- local instance (M : Mag) : Mul M where mul := M.op
local instance (M : Mag) : CoeFun M (fun _ => M → M) where coe := M.op

theorem Mag.triv {M : Mag} (a : M) : a a = a a := rfl

structure SGrp extends Mag where
  -- assoc (a b c : toMag) : op (op a b) c = op a (op b c)
  assoc (a b c : carrier) : a b c = a (b c)
  -- assoc (a b c : carrier) : (a * b) * c = a * (b * c)

structure Mon extends SGrp where
  unit : carrier
  unitl (a : carrier) : unit a = a
  unitr (a : carrier) : a unit = a
-- local instance : CoeSort Mon (Type u) where coe M := M.carrier
local instance (M : Mon) : OfNat M.toMag (nat_lit 1) where ofNat := M.unit

structure Grp extends Mon where
  inv : carrier → carrier
  invl (a : carrier) : (inv a) a = a
  invr (a : carrier) : a (inv a) = a
-- local instance : CoeSort Grp (Type u) where coe G := G.carrier
local instance (G : Grp) : Inv G.toMag where inv := G.inv

structure Ab extends Grp where
  comm (a b : carrier) : a b = b a