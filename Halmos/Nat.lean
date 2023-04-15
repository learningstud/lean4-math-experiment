set_option linter.unusedVariables false
set_option autoImplicit false

inductive ℕ
  | zero : ℕ
  /-- The successor function a la Peano -/
  | succ : ℕ → ℕ
namespace ℕ

@[inherit_doc] postfix:arg "⁺" => succ
@[default_instance] instance: OfNat ℕ (nat_lit 0) where ofNat := zero
@[default_instance] instance: OfNat ℕ (nat_lit 1) where ofNat := zero⁺

variable {a b c: ℕ}
/-! ## Successor -/

theorem zero_succ_one: 0⁺ = 1 := rfl
example: a = b → a⁺ = b⁺ :=
  congrArg succ
theorem succ_congr {f g: ℕ → ℕ} (n: ℕ): f n = g n → (f n)⁺ = (g n)⁺ :=
  congrArg succ

example: a⁺ = b⁺ → a = b := succ.inj
example: a⁺ ≠ 0 := ℕ.noConfusion
example: 0 ≠ a⁺ := ℕ.noConfusion
theorem succ_ne_self: a⁺ ≠ a :=
  a.rec ℕ.noConfusion fun _ ih h => ih (succ.inj h)

/-! ## Addtion -/

def add (m: ℕ): ℕ → ℕ | 0 => m | n⁺ => (add m n)⁺
instance: Add ℕ where add := add

theorem add_succ: a + b⁺ = (a + b)⁺ := rfl
theorem succ_add: a⁺ + b = (a + b)⁺ := b.rec rfl succ_congr
theorem add_zero: a + 0 = a := rfl
theorem zero_add: 0 + a = a := a.rec rfl succ_congr
theorem add_one: a + 1 = a⁺ := rfl
theorem one_add: 1 + a = a⁺ := succ_add ▸ congrArg succ zero_add
theorem add_assoc: a + (b + c) = (a + b) + c := c.rec rfl succ_congr
theorem add_comm: b + a = a + b :=
  b.rec zero_add fun _ h => succ_add ▸ (congrArg succ h)
theorem add_cancel: a + c = b + c → a = b :=
  c.rec id fun _ ih h => ih (succ.inj h)
theorem add_cancel_zero: a + c = c → a = 0
  | h => add_cancel (h.trans zero_add.symm)
theorem cancel_add: c + a = c + b → a = b
  | h => add_cancel ((add_comm ▸ h).trans add_comm)
theorem cancel_add_zero: c + a = c → a = 0 := @cancel_add a 0 c
theorem add_pos: a + b = 0 → a = 0 ∧ b = 0 :=
  fun h => match a, b with | 0, 0 => ⟨rfl, rfl⟩ | _, _⁺ => ℕ.noConfusion h

/-! ## Multiplication -/

def mul (m: ℕ): ℕ → ℕ | 0 => 0 | n⁺ => (mul m n) + m
instance: Mul ℕ where mul := mul

theorem mul_succ: a * b⁺ = a * b + a := rfl
theorem succ_mul: a⁺ * b = a * b + b :=
  b.rec rfl fun b h => by
    rw [mul_succ, h, add_succ, ←add_assoc, @add_comm a, add_assoc] ; rfl
theorem mul_zero: a * 0 = 0 := rfl
theorem zero_mul: 0 * a = 0 := a.rec rfl fun _ h => mul_succ ▸ h
theorem mul_one: a * 1 = a :=
  by rw [←zero_succ_one, mul_succ, mul_zero, zero_add]
theorem one_mul: 1 * a = a :=
  a.rec rfl fun a h => by rw [mul_succ, h, add_one]
theorem add_mul: (a + b) * c = a * c + b * c :=
  c.rec rfl fun c h => by rw [
    mul_succ, mul_succ, mul_succ, h, ←add_assoc,
    @add_assoc (b*c), @add_comm a, ←@add_assoc a, add_assoc
  ]
theorem mul_add: a * (b + c) = a * b + a * c :=
  c.rec rfl fun c h => by rw [add_succ, mul_succ, mul_succ, add_assoc, h]
theorem mul_assoc: a * (b * c) = (a * b) * c :=
  c.rec rfl fun c h => by rw [mul_succ, mul_succ, mul_add, h]
theorem mul_comm: b * a = a * b :=
  b.rec zero_mul fun c h => by rw [succ_mul, mul_succ, h]
theorem mul_comm': a * (b * c) = b * (a * c) :=
  c.rec rfl fun c ih => by rw
    [mul_succ, mul_succ, mul_add, mul_add, ih, @mul_comm a b]
-- theorem mul_pos': ∀ (a b : ℕ), a ≠ 0 → b ≠ 0 → a * b ≠ 0
--   | _⁺, _⁺, _, _ => mul_succ ▸ succ_ne_zero
theorem mul_pos: a * b = 0 → a = 0 ∨ b = 0 :=
  fun h => match b with
  | 0 => .inr rfl
  | _⁺ => .inl (add_pos (mul_succ ▸ h)).right
theorem cancel_mul (hc: c ≠ 0): c * a = c * b → a = b :=
  a |> show ∀ a: ℕ, c * a = c * b → a = b from
  b.rec (fun _ h => (mul_pos h).elim (absurd . hc) id) fun _ ih a h' =>
    match a with
    | 0 => (mul_pos h'.symm).elim (absurd . hc) .symm
    | a⁺ => congrArg succ (ih a (add_cancel h'))
theorem mul_cancel (hx: c ≠ 0): a * c = b * c → a = b
  | h => cancel_mul hx ((mul_comm.trans h).trans mul_comm)

/-! ## Exponential -/

def pow (m: ℕ): ℕ → ℕ | 0 => 1 | n⁺ => (pow m n) * m
instance: Pow ℕ ℕ where pow := pow

theorem pow_succ: a^b⁺ = a^b * a := rfl
-- theorem succ_pow: a⁺^b = a^b 
theorem pow_zero: a^0 = 1 := rfl
theorem pow_zero': a^zero = 1 := rfl -- FIXME: redundant
example: 0^0 = 1 := pow_zero
theorem zero_pow_succ: 0^a⁺ = 0 := rfl
theorem pow_one: a^1 = a :=
  by rw [←zero_succ_one, pow_succ, pow_zero, one_mul]
theorem one_pow: 1^a = 1 :=
  a.rec rfl fun a h => by rw [pow_succ, h] ; rfl
theorem pow_add: a^(b + c) = a^b * a^c :=
  c.rec (by rw [pow_zero', mul_one] ; rfl) fun c ih => by rw
    [pow_succ, add_succ, pow_succ, ih, mul_assoc]
theorem pow_mul: a^(b * c) = (a^b)^c :=
  c.rec rfl fun c ih => by rw [mul_succ, pow_add, pow_succ, ih]
theorem mul_pow: (a * b)^c = a^c * b^c :=
  c.rec rfl fun c ih => by rw
    [pow_succ, pow_succ, pow_succ, ih, ←mul_assoc, @mul_comm' (b^c), mul_assoc]
theorem pow_comm': (a^b)^c = (a^c)^b :=
  by rw [←pow_mul, ←pow_mul, mul_comm]

section
@[default_instance] local instance: OfNat ℕ (nat_lit 2) where ofNat := 1⁺
private theorem zero_succ_succ : 2 = 0⁺⁺ := rfl
private theorem one_add_one : 1 + 1 = 2 := rfl
private theorem two_mul : 2 * a = a + a :=
  by rw [←one_add_one, add_mul, one_mul]

private def square (n : ℕ) := n^2
local postfix:arg "²" => square
private theorem square_mul : a² = a * a :=
  by rw [square, zero_succ_succ, pow_succ, pow_succ, pow_zero, one_mul]
example : (a + b)² = a² + 2 * a * b + b² :=
  by rw [
    square_mul, add_mul, mul_add, ←square_mul, mul_add, ←square_mul,
    add_assoc, ←@add_assoc a², @mul_comm a, ←two_mul, mul_assoc
  ]
end

/-! ## Order -/

/-- existentially-defined partial order -/
def existential_le (m n: ℕ) := ∃ k : ℕ, n = m + k
/-- inductively-defined partial order -/
inductive inductive_le (n: ℕ): ℕ → Prop
  /-- Less-equal is reflexive: `n ≤ n` -/
  | refl: inductive_le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m: ℕ}: inductive_le n m → inductive_le n m⁺

namespace existential_le
local instance: LE ℕ where le := existential_le

private theorem le_succ_self: a ≤ a⁺ := ⟨1, add_one⟩
private theorem le_refl: a ≤ a := ⟨0, rfl⟩
private theorem le_succ: a ≤ b → a ≤ b⁺ | ⟨k, h⟩ => ⟨k⁺, congrArg succ h⟩
private theorem zero_le: 0 ≤ a := ⟨a, zero_add.symm⟩
private theorem le_trans: a ≤ b → b ≤ c → a ≤ c
  | ⟨k, h⟩, ⟨k', h'⟩ => ⟨k + k', by rw [h', h, add_assoc]⟩
private theorem le_antisymm: a ≤ b → b ≤ a → a = b
  | ⟨k, h⟩, ⟨k', h'⟩ => by
    rw [h, ←add_assoc] at h'
    have h' := cancel_add (show a + 0 = a + (k + k') from h')
    have h₀ := (add_pos h'.symm).left
    rw [h₀] at h
    exact h.symm
private theorem le_zero: a ≤ 0 → a = 0
  | ⟨_, h⟩ => (add_pos h.symm).left
private theorem succ_le_succ: a ≤ b → a⁺ ≤ b⁺
  | ⟨k, h⟩ => ⟨k, congrArg succ h ▸ succ_add.symm⟩
private theorem le_total: a ≤ b ∨ b ≤ a :=
  b.rec (.inr zero_le) fun _ ih => ih.elim (.inl ∘ le_succ) fun ⟨k, h'⟩ =>
  match k with
  | 0 => .inl (h' ▸ le_succ_self)
  | k⁺ => .inr ⟨k, succ_add ▸ h'⟩
private theorem le_add: a ≤ b → ∀ t, a + t ≤ b + t
  | h => rec h fun _ => succ_le_succ
private theorem add_le: a ≤ b → ∀ t, t + a ≤ t + b
  | h, t => by rw [add_comm, @add_comm b] ; exact le_add h t
private theorem succ_le: a⁺ ≤ b⁺ → a ≤ b
  | ⟨k, h⟩ => ⟨k, succ.inj (succ_add ▸ h)⟩
private theorem not_succ_le_self: ¬(a⁺ ≤ a)
  | ⟨k, h⟩ => by
    rw [succ_add, ←add_succ] at h
    have := cancel_add_zero h.symm
    contradiction
-- level 15
end existential_le

theorem le_equiv {m n : ℕ}: existential_le m n ↔ inductive_le m n :=
  ⟨
  n.rec
    (fun ⟨_, h⟩ => (add_pos h.symm).left ▸ .refl)
    fun _ ih ⟨k, h⟩ => match k with
      | 0 => h ▸ .refl
      | k⁺ => (ih ⟨k, succ.inj h⟩).step
  ,
  fun h => h.rec existential_le.le_refl fun _ => existential_le.le_succ
  ⟩

instance: LE ℕ where le := inductive_le
instance: LT ℕ where lt m n := m⁺ ≤ n

theorem le_succ: a ≤ a⁺ := .step .refl
theorem lt_succ: a < a⁺ := .refl
theorem le_refl: a ≤ a := .refl
theorem not_succ_le_zero: ¬(a < 0) := (nomatch .)
theorem le_trans: a ≤ b → b ≤ c → a ≤ c
  | h, h' => h'.rec h fun _ => .step
theorem lt_is_le: a < b → a ≤ b
  | h => le_trans le_succ h
theorem le_of_succ_le_succ: a⁺ ≤ b⁺ → a ≤ b
  | .refl => .refl
  | .step h => lt_is_le h
theorem lt_irrefl: ¬(a < a) :=
  a.rec not_succ_le_zero fun _ h h' => h (le_of_succ_le_succ h')
theorem not_succ_le_self: ¬(a⁺ ≤ a) := lt_irrefl
theorem not_succ_lt_self: ¬(a⁺ < a)
  | h => lt_irrefl (lt_is_le h)
theorem le_step: a ≤ b → a ≤ b⁺ := .step
theorem lt_step: a < b → a < b⁺ := .step
theorem step_le: a⁺ ≤ b → a ≤ b := lt_is_le
theorem step_lt: a⁺ < b → a < b := step_le
theorem zero_le: 0 ≤ a := a.rec .refl fun _ => .step
theorem zero_lt: a ≠ 0 → 0 < a :=
  a.rec (absurd rfl) fun
    | 0, _, _ => .refl
    | _⁺, ih, _ => (ih ℕ.noConfusion).step
theorem le_zero: a ≤ 0 → a = 0
  | _ => match a with | 0 => rfl
theorem le_antisymm: a ≤ b → b ≤ a → a = b
  | .refl, _ => rfl
  | .step h, h' => absurd (le_trans h' h) lt_irrefl
theorem succ_le_succ: a ≤ b → a⁺ ≤ b⁺
  | h => h.rec .refl fun _ => .step
theorem le_total: a ≤ b ∨ b ≤ a :=
  b.rec (.inr zero_le) fun _ ih => ih.elim (.inl ∘ .step) fun
    | .refl => .inl le_succ
    | .step h => .inr (succ_le_succ h)
theorem le_add: a ≤ b → ∀ t, a + t ≤ b + t
  | h => h.rec (fun _ => .refl) fun _ ih t => succ_add ▸ (ih t).step
theorem add_le: a ≤ b → ∀ t, t + a ≤ t + b
  | h, t => by rw [add_comm, @add_comm b] ; exact le_add h t

/-! ## Pred and Sub -/

def pred: ℕ → ℕ | 0 => 0 | n⁺ => n
/-- Cut off at `0` -/
def sub (m: ℕ): ℕ → ℕ | 0 => m | n⁺ => pred (sub m n)
-- instance: Sub ℕ where sub := sub

theorem succ_sub_succ_eq_sub (m n: ℕ): m⁺.sub n⁺ = m.sub n :=
  n.rec rfl fun _ ih => congrArg pred ih

theorem pred_le: (n: ℕ) → pred n ≤ n
  | 0 => .refl
  | _⁺ => le_succ

theorem pred_lt: {n: ℕ} → n ≠ 0 → pred n < n
  | 0, h => absurd rfl h
  | _⁺, _ => succ_le_succ .refl

theorem sub_le (m n: ℕ): m.sub n ≤ m :=
  n.rec .refl fun n ih => le_trans (pred_le (m.sub n)) ih

theorem sub_lt: {m n: ℕ} → 0 < m → 0 < n → m.sub n < m
  | 0, _, h, _ => absurd h (@lt_irrefl 0)
  | _⁺, 0, _, h => absurd h (@lt_irrefl 0)
  | m⁺, n⁺, _,  _ => (succ_sub_succ_eq_sub m n).symm ▸
      show m.sub n < m⁺ from succ_le_succ (sub_le m n)


/-! ## Decidable -/
#check Nat.decLe

protected def ble: ℕ → ℕ → Bool
  | 0, _ => true
  | _⁺, 0 => false
  | m⁺, n⁺ => ℕ.ble m n
infix:50 " ≤? " => ℕ.ble

theorem le_of_ble_eq_true: {m n: ℕ} → m ≤? n → m ≤ n
  | 0, _, _ => zero_le
  | _⁺, _⁺, h => succ_le_succ (le_of_ble_eq_true h)

theorem ble_self_eq_true: (n: ℕ) → n ≤? n
  | 0 => rfl
  | n⁺ => ble_self_eq_true n

theorem ble_succ_eq_true: {m n: ℕ} → m ≤? n → m ≤? n⁺ 
  | 0, _, _ => rfl
  | m⁺, _⁺, h => ble_succ_eq_true (m := m) h

theorem ble_eq_true_of_le {m n: ℕ}: m ≤ n → m ≤? n
  | .refl => ble_self_eq_true m
  | .step h => ble_succ_eq_true (ble_eq_true_of_le h)

theorem not_le_of_not_ble_eq_true {m n: ℕ}: ¬(m ≤? n) → ¬(m ≤ n)
  | h, h' => absurd (ble_eq_true_of_le h') h

instance decLe (m n: ℕ): Decidable (m ≤ n) :=
  if h: m ≤? n
  then isTrue (le_of_ble_eq_true h)
  else isFalse (not_le_of_not_ble_eq_true h)

instance decLt (m n: ℕ): Decidable (m < n) :=
  decLe m⁺ n

/-! ## Modulus -/
#check Nat.mod
#check Nat.div_rec_lemma

theorem div_rec_lemma {a b: ℕ}: 0 < b ∧ b ≤ a → a.sub b < a
  | ⟨h, h'⟩ => sub_lt (le_trans h h') h

-- protected def mod (m n: ℕ): ℕ :=
--   if 0 < n ∧ n ≤ m then ℕ.mod (m.sub n) n else m
-- termination_by' measure fun ⟨m, n⟩ => sub m n
-- decreasing_by simp_wf; 
  -- suffices ∀ {a b: ℕ}, 0 < b ∧ b ≤ a → sizeOf (a.sub b) < sizeOf a
  -- from by simp_wf; apply this ; assumption
  -- exact fun | ⟨h, h'⟩ => by simp ; unfold sizeOf ; 
#check sizeOf

end ℕ

class Poset (α: Type _) where
  rel: α → α → Prop
  refl (x: α): rel x x
  trans (x y z: α): rel x y → rel y z → rel x z
  antisymm (x y: α): rel x y → rel y x → x = y

class StrictPoset (α: Type _) where
  rel: α → α → Prop
  irrefl (x: α): ¬rel x x
  trans (x y z: α): rel x y → rel y z → rel x z
  asymm (x y: α): rel x y → ¬rel y x
