-- import Algebra.Group
import Algebra.Basic

/-
local instance addMag (α : Type u) [A : Add α] : Mag := { carrier := α, op := A.add }
local instance [A : Add α] : CoeDep _ α Mag where coe := { carrier := α, op := A.add }
local instance [Add α] : Coe α (addMag α).carrier where coe a := a
local instance [Add α] : Coe (addMag α).carrier α where coe a := a
-- instance : CoeSort Mag (Type u) where coe M := M.carrier
example [Add α] (a : α) : a + a = a + a := @Mag.triv α a

local instance mulMag [M : Mul α] : Mag := { carrier := α, op := M.mul }
-- instance {α : Type u} [M : Mul α] : CoeDep (Type u) α Mag where
--   coe := mulMag M
-- example [Mul α] (a : α) : a * a = a * a := Mag.triv a
-/

variable (α : Type u)

/-! ## Additive -/

class AddComm extends Add α where
  add_comm (a b : α) : b + a = a + b
class AddSGrp extends Add α where
  add_assoc (a b c : α) : a + (b + c) = (a + b) + c
class AddMon extends AddSGrp α, Zero α where
  zero_add (a : α) : 0 + a = a
  add_zero (a : α) : a + 0 = a
class AddCommMon extends AddMon α, AddComm α
-- instance [AddMon α] [A : AddComm α] : AddCommMon α where
--   add_comm := A.add_comm

class AddCancelLeft extends Add α where
  cancel_add (a b x : α) : x + a = x + b → a = b
class AddCancelRight extends Add α where
  add_cancel (a b x : α) : a + x = b + x → a = b
class AddCancel extends AddCancelLeft α, AddCancelRight α

class AddCommCancelLeft extends AddComm α, AddCancelLeft α
instance [A : AddCommCancelLeft α] : AddCancel α where
  cancel_add := A.cancel_add
  add_cancel a b x h := A.cancel_add a b x
    (((A.add_comm a x).trans h).trans (A.add_comm x b))

class AddCommCancelRight extends AddComm α, AddCancelRight α
instance [A : AddCommCancelRight α] : AddCancel α where
  add_cancel := A.add_cancel
  cancel_add a b x h := A.add_cancel a b x
    (((A.add_comm x a).trans h).trans (A.add_comm b x))

/-! ## Multiplicative -/

class MulSGrp extends Mul α where
  mul_assoc (a b c : α) : a * (b * c) = (a * b) * c
class MulMon extends MulSGrp α, One α where
  one_mul (a : α) : 1 * a = a
  mul_one (a : α) : a * 1 = a
class MulComm extends Mul α where
  mul_comm (a b : α) : b * a = a * b
class MulCommMon extends MulMon α, MulComm α

class MulCancelLeft extends Mul α where
  cancel_mul (a b x : α) : x * a = x * b → a = b
class MulCancelRight extends Mul α where
  mul_cancel (a b x : α) : a * x = b * x → a = b
class MulCancel extends MulCancelLeft α, MulCancelRight α