variable (α : Type u)

class Zero where zero : α
instance [z : Zero α] : OfNat α (nat_lit 0) where ofNat := z.zero
instance [OfNat α (nat_lit 0)] : Zero α where zero := 0
-- instance [z : Zero α] [Coe α β] : Zero β where zero := z.zero

class One where one : α
instance [o : One α] : OfNat α (nat_lit 1) where ofNat := o.one
-- instance [o : One α] [Coe α β] : One β where one := o.one

class Inv where inv : α → α
postfix:77 "⁻¹" => Inv.inv

-- class Succ where succ : α → α
-- postfix:100 "⁺" => Succ.succ
-- attribute [match_pattern] Succ.succ

class HAbs (α : outParam (Type u)) (β : Type v) where hAbs : α → β
-- class HAbs (α : Type u) (β : Type v) where hAbs : α → β
macro:arg "∣" a:term "∣" : term => `(HAbs.hAbs $a)

instance [Add α] [Neg α] : Sub α where sub a b := a + (-b)