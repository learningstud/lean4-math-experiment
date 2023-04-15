inductive NaturalNumber
  /-- The initial element of a Peano system is often denoted by `0`. -/
  | initialElement : NaturalNumber
  /-- The successor function of a Peano system is often denoted by `S` or `⬝⁺` -/
  | successor : NaturalNumber → NaturalNumber

example (m n : NaturalNumber) : m = n ↔ m.successor = n.successor :=
  ⟨congrArg _, NaturalNumber.successor.inj⟩
example (n : NaturalNumber) : n.successor ≠ NaturalNumber.initialElement :=
  fun _ => by contradiction

abbrev ℕ := NaturalNumber

@[default_instance]
instance : OfNat ℕ (nat_lit 0) where
  ofNat := .initialElement
#check 0

@[inherit_doc]
postfix:100 "⁺" => NaturalNumber.successor

@[default_instance]
instance : OfNat ℕ (nat_lit 1) where
  ofNat := 0⁺
#check 1
example : 1 = 0⁺ := rfl

instance : Add ℕ where
  add := add
where add (m : ℕ)
  | 0 => m
  | n⁺ => (add m n)⁺

theorem ℕ.add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) :=
  NaturalNumber.recOn c rfl fun _ h => congrArg _ h
  -- by induction c with
  -- | initialElement => rfl
  -- | _ c h => exact congrArg _ h