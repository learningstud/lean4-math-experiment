import Algebra.Ring

set_option linter.unusedVariables false

inductive ℕ
  | zero : ℕ
  /-- The successor function a la Peano -/
  | succ : ℕ → ℕ
namespace ℕ

@[inherit_doc] postfix:arg "⁺" => succ
@[default_instance] instance : OfNat ℕ (nat_lit 0) where ofNat := zero
@[default_instance] instance : OfNat ℕ (nat_lit 1) where ofNat := zero⁺

variable {a b c x : ℕ}
/-! ## Successor -/

theorem zero_succ_one : 0⁺ = 1 :=
  rfl
theorem succ_congr_arg : a = b → a⁺ = b⁺ :=
  congrArg succ
theorem succ_congr_fun {f g : ℕ → ℕ} (n : ℕ) : f n = g n → (f n)⁺ = (g n)⁺ :=
  succ_congr_arg

example : a⁺ = b⁺ → a = b :=
  succ.inj
theorem succ_ne_zero : a⁺ ≠ 0 :=
  fun h => by contradiction
theorem zero_ne_succ : 0 ≠ a⁺ :=
  fun h => succ_ne_zero h.symm
theorem succ_ne_self : a⁺ ≠ a :=
  a.rec succ_ne_zero fun _ ih h => ih (succ.inj h)

/-! ## Addtion -/

def add (m : ℕ) : ℕ → ℕ | 0 => m | n⁺ => (add m n)⁺
instance : Add ℕ where add := add

theorem add_succ : a + b⁺ = (a + b)⁺ :=
  rfl
theorem succ_add : a⁺ + b = (a + b)⁺ :=
  rec rfl succ_congr_fun b
theorem add_zero : a + 0 = a :=
  rfl
theorem zero_add : 0 + a = a :=
  rec rfl succ_congr_fun a
theorem add_one : a + 1 = a⁺ :=
  rfl
theorem one_add : 1 + a = a⁺ :=
  succ_congr_arg zero_add ▸ succ_add
theorem add_assoc : a + (b + c) = (a + b) + c :=
  rec rfl succ_congr_fun c
theorem add_comm : b + a = a + b :=
  b.rec zero_add fun _ h => succ_add.trans (succ_congr_arg h)
theorem add_cancel : a + x = b + x → a = b :=
  x.rec id fun _ ih h => ih (succ.inj h)
theorem add_cancel_zero : a + x = x → a = 0 :=
  fun h => add_cancel (calc
    a + x = x     := h
        _ = 0 + x := zero_add.symm
  )
theorem cancel_add : x + a = x + b → a = b :=
  fun h => add_cancel ((add_comm.trans h).trans add_comm)
theorem cancel_add_zero : x + a = x → a = 0 :=
  @cancel_add a 0 x
theorem add_pos : a + b = 0 → a = 0 ∧ b = 0 :=
  fun h => match a, b with
  | 0, 0 => ⟨rfl, rfl⟩
  | 0, _⁺ => (succ_ne_zero h).elim
  | _⁺, 0 => (succ_ne_zero h).elim

/-! ## Multiplication -/

def mul (m : ℕ) : ℕ → ℕ | 0 => 0 | n⁺ => (mul m n) + m
instance : Mul ℕ where mul := mul

theorem mul_succ : a * b⁺ = a * b + a :=
  rfl
theorem succ_mul : a⁺ * b = (a * b) + b :=
  b.rec rfl fun b h => by
    rw [mul_succ, h, add_succ, ←add_assoc, @add_comm a, add_assoc] ; rfl
theorem mul_zero : a * 0 = 0 :=
  rfl
theorem zero_mul : 0 * a = 0 :=
  a.rec rfl fun _ h => mul_succ ▸ h
theorem mul_one : a * 1 = a :=
  by rw [←zero_succ_one, mul_succ, mul_zero, zero_add]
theorem one_mul : 1 * a = a :=
  a.rec rfl fun a h => by rw [mul_succ, h, add_one]
theorem add_mul : (a + b) * c = a * c + b * c :=
  c.rec rfl fun c h => by rw [
    mul_succ, mul_succ, mul_succ, h, ←add_assoc,
    @add_assoc (b*c), @add_comm a, ←@add_assoc a, add_assoc
  ]
theorem mul_add : a * (b + c) = a * b + a * c :=
  c.rec rfl fun c h => by rw [add_succ, mul_succ, mul_succ, add_assoc, h]
theorem mul_assoc : a * (b * c) = (a * b) * c :=
  c.rec rfl fun c h => by rw [mul_succ, mul_succ, mul_add, h]
theorem mul_comm : b * a = a * b :=
  b.rec zero_mul fun c h => by rw [succ_mul, mul_succ, h]
theorem mul_comm' : a * (b * c) = b * (a * c) :=
  c.rec rfl fun c ih => by rw
    [mul_succ, mul_succ, mul_add, mul_add, ih, @mul_comm a b]
-- theorem mul_pos' : ∀ (a b : ℕ), a ≠ 0 → b ≠ 0 → a * b ≠ 0
--   | _⁺, _⁺, _, _ => mul_succ ▸ succ_ne_zero
theorem mul_pos : a * b = 0 → a = 0 ∨ b = 0 :=
  fun h => match b with
  | 0 => .inr rfl
  | b⁺ => .inl (add_pos (mul_succ ▸ h)).right
theorem cancel_mul (hx : x ≠ 0) : x * a = x * b → a = b :=
  a |> show ∀ a : ℕ, x * a = x * b → a = b from
  b.rec (fun a h => (mul_pos h).elim (absurd . hx) id) fun b ih a h' =>
    match a with
    | 0 => (mul_pos h'.symm).elim (absurd . hx) .symm
    | a⁺ => succ_congr_arg (ih a (add_cancel h'))
theorem mul_cancel (hx : x ≠ 0) : a * x = b * x → a = b :=
  fun h => cancel_mul hx ((mul_comm.trans h).trans mul_comm)

/-! ## Exponential -/

def pow (m : ℕ) : ℕ → ℕ | 0 => 1 | n⁺ => (pow m n) * m
instance : Pow ℕ ℕ where pow := pow

theorem pow_succ : a^b⁺ = a^b * a :=
  rfl
-- theorem succ_pow : a⁺^b = a^b 
theorem pow_zero : a^0 = 1 :=
  rfl
theorem pow_zero' : a^zero = 1 := -- FIXME: redundant
  rfl
example : 0^0 = 1 :=
  pow_zero
theorem zero_pow_succ : 0^a⁺ = 0 :=
  rfl
theorem pow_one : a^1 = a :=
  by rw [←zero_succ_one, pow_succ, pow_zero, one_mul]
theorem one_pow : 1^a = 1 :=
  a.rec rfl fun a h => by rw [pow_succ, h] ; rfl
theorem pow_add : a^(b + c) = a^b * a^c :=
  c.rec (by rw [pow_zero', mul_one] ; rfl) fun c ih => by rw
    [pow_succ, add_succ, pow_succ, ih, mul_assoc]
theorem pow_mul : a^(b * c) = (a^b)^c :=
  c.rec rfl fun c ih => by rw [mul_succ, pow_add, pow_succ, ih]
theorem mul_pow : (a * b)^c = a^c * b^c :=
  c.rec rfl fun c ih => by rw
    [pow_succ, pow_succ, pow_succ, ih, ←mul_assoc, @mul_comm' (b^c), mul_assoc]
theorem pow_comm' : (a^b)^c = (a^c)^b :=
  by rw [←pow_mul, ←pow_mul, mul_comm]

section
@[default_instance] local instance : OfNat ℕ (nat_lit 2) where ofNat := 1⁺
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
#check Nat.le

/-- existentially-defined partial order -/
def existential_le (m n : ℕ) := ∃ k : ℕ, n = m + k
/-- inductively-defined partial order -/
inductive inductive_le (n : ℕ) : ℕ → Prop
  /-- Less-equal is reflexive: `n ≤ n` -/
  | refl : inductive_le n n
  /-- If `n ≤ m`, then `n ≤ m + 1`. -/
  | step {m : ℕ} : inductive_le n m → inductive_le n m⁺

namespace existential_le
local instance : LE ℕ where le := existential_le

private theorem le_succ_self : a ≤ a⁺ :=
  ⟨1, add_one⟩
private theorem le_refl : a ≤ a :=
  ⟨0, rfl⟩
private theorem le_succ : a ≤ b → a ≤ b⁺ :=
  fun ⟨k, h⟩ => ⟨k⁺, succ_congr_arg h⟩
private theorem zero_le : 0 ≤ a :=
  ⟨a, zero_add.symm⟩
private theorem le_trans : a ≤ b → b ≤ c → a ≤ c :=
  fun ⟨k, h⟩ ⟨k', h'⟩ => ⟨k + k', by rw [h', h, add_assoc]⟩
private theorem le_antisymm : a ≤ b → b ≤ a → a = b :=
  fun ⟨k, h⟩ ⟨k', h'⟩ => by
    rw [h, ←add_assoc] at h'
    have h' := cancel_add (show a + 0 = a + (k + k') from h')
    have h₀ := (add_pos h'.symm).left
    rw [h₀] at h
    exact h.symm
private theorem le_zero : a ≤ 0 → a = 0 :=
  fun ⟨k, h⟩ => (add_pos h.symm).left
private theorem succ_le_succ : a ≤ b → a⁺ ≤ b⁺ :=
  fun ⟨k, h⟩ => ⟨k, succ_congr_arg h ▸ succ_add.symm⟩
private theorem le_total : a ≤ b ∨ b ≤ a :=
  b.rec (.inr zero_le) fun b ih => ih.elim (.inl ∘ le_succ) fun ⟨k, h'⟩ =>
  match k with
  | 0 => .inl (h' ▸ le_succ_self)
  | k⁺ => .inr ⟨k, succ_add ▸ h'⟩
private theorem le_add : a ≤ b → ∀ t, a + t ≤ b + t :=
  fun h => rec h fun t ih => succ_le_succ ih
private theorem add_le : a ≤ b → ∀ t, t + a ≤ t + b :=
  fun h t => by rw [add_comm, @add_comm b] ; exact le_add h t
private theorem succ_le : a⁺ ≤ b⁺ → a ≤ b :=
  fun ⟨k, h⟩ => ⟨k, succ.inj (succ_add ▸ h)⟩
private theorem not_succ_le_self : ¬(a⁺ ≤ a) :=
  fun ⟨k, h⟩ => by
    rw [succ_add, ←add_succ] at h
    have := cancel_add_zero h.symm
    exact succ_ne_zero this
-- level 15
end existential_le

section
@[inherit_doc] local infix:50 " ≤E "  => existential_le
@[inherit_doc] local infix:50 " ≤I "  => inductive_le

variable {m n : ℕ}
private theorem existential_le_inductive : m ≤E n → m ≤I n :=
  n.rec
    (fun ⟨k, h⟩ => (add_pos h.symm).left ▸ .refl)
    fun n ih ⟨k, h⟩ => match k with
      | 0 => h ▸ .refl
      | k⁺ => (ih ⟨k, succ.inj h⟩).step
private theorem inductive_le_existential : m ≤I n → m ≤E n :=
  fun h => h.rec
    existential_le.le_refl
    fun _ => existential_le.le_succ -- Why?
theorem le_equiv : m ≤E n ↔ m ≤I n :=
  ⟨existential_le_inductive, inductive_le_existential⟩
end

local instance : LE ℕ where le := inductive_le
local instance : LT ℕ where lt m n := m⁺ ≤ n

theorem le_succ : a ≤ a⁺ :=
  .step .refl
theorem lt_succ : a < a⁺ :=
  .refl -- constructor
theorem le_refl : a ≤ a :=
  .refl -- constructor
theorem lt_irrefl : ¬(a < a) :=
  a.rec (fun h => nomatch h) sorry
theorem not_succ_le : ¬(a⁺ ≤ a) :=
  lt_irrefl
theorem not_succ_lt : ¬(a⁺ < a) :=
  sorry
theorem lt_is_le : a < b → a ≤ b :=
  fun h => h.rec le_succ fun _ => .step
theorem le_step : a ≤ b → a ≤ b⁺ :=
  .step
theorem lt_step : a < b → a < b⁺ :=
  .step
theorem step_le : a⁺ ≤ b → a ≤ b :=
  lt_is_le -- same as `lt_is_le`
theorem step_lt : a⁺ < b → a < b :=
  step_le
theorem zero_le : 0 ≤ a :=
  a.rec .refl fun _ => .step
theorem zero_lt : a ≠ 0 → 0 < a :=
  sorry
theorem le_zero : a ≤ 0 → a = 0 :=
  a.casesOn (fun _ => rfl) fun _ h => nomatch h

theorem le_trans : a ≤ b → b ≤ c → a ≤ c :=
  fun hab hbc => hbc.rec hab fun _ => .step
theorem le_antisymm : a ≤ b → b ≤ a → a = b :=
  fun | .refl => fun _ => rfl | .step h => sorry
#check Nat.le_antisymm
theorem succ_le_succ {a b : ℕ} : a ≤ b → a⁺ ≤ b⁺ :=
  fun h => h.rec .refl fun _ => .step
theorem le_total : a ≤ b ∨ b ≤ a :=
  b.rec (.inr zero_le) fun b ih => ih.elim (.inl ∘ .step)
    fun | .refl => .inl (.step .refl)
        | .step h => .inr (succ_le_succ h)
theorem le_add : a ≤ b → ∀ t, a + t ≤ b + t :=
  sorry
theorem add_le : a ≤ b → ∀ t, t + a ≤ t + b :=
  sorry
theorem succ_le : a⁺ ≤ b⁺ → a ≤ b :=
  fun h => match h with | .refl => .refl | .step g => sorry
theorem not_succ_le_self : ¬(a⁺ ≤ a) :=
  a.rec (fun h => nomatch h) fun a ih h => ih (succ_le h)

def pred : ℕ → ℕ | 0 => 0 | n⁺ => n
/-- Cut off at `0` -/
def sub (m : ℕ) : ℕ → ℕ | 0 => m | n⁺ => pred (sub m n)
-- instance : Sub ℕ where sub := sub

end ℕ

class Poset (α : Type u) where
  rel : α → α → Prop
  refl (x : α) : rel x x
  trans (x y z : α) : rel x y → rel y z → rel x z
  antisymm (x y : α) : rel x y → rel y x → x = y

class StrictPoset (α : Type u) where
  rel : α → α → Prop
  irrefl (x : α) : ¬rel x x
  trans (x y z : α) : rel x y → rel y z → rel x z
  asymm (x y : α) : rel x y → ¬rel y x
