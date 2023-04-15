set_option autoImplicit false

#check Int
#check OfScientific

abbrev ℕ := Nat

theorem Nat.lt_of_succ_sub_eq_zero {m n: ℕ}: m.succ - n = 0 → m < n
  | h => Nat.zero_add n ▸ le_add_of_sub_le (Nat.le_of_eq h)
-- theorem Nat.lt_of_sub_succ_eq_zero {m n: ℕ}: m - n.succ = 0 → m < n
--   | h => Nat.zero_add n ▸ le_add_of_sub_le (Nat.le_of_eq h)
theorem Nat.succ_sub_sub_one (m n: ℕ): m.succ - n - 1 = m - n :=
  calc m.succ - n - 1
      = m.succ - (n + 1) := Nat.sub_sub _ _ _
    _ = m.succ - n.succ := rfl
    _ = m - n := Nat.succ_sub_succ _ _
#check Nat.sub
theorem Nat.one_sub_succ (m n: ℕ): 1 - (m.succ - n) = n - m :=
  sorry

abbrev ℤ := Int

namespace Int

variable (m n: ℕ) (a b c: ℤ)

#check Nat.sub
example: n - 0 = n := rfl
example: 0 - n = 0 := Nat.zero_sub n
example: subNatNat 0 n.succ = negSucc n := rfl
theorem subNatNat_zero: subNatNat n 0 = n := by unfold subNatNat ; simp
theorem subNatNat_self: subNatNat n n = 0 := by unfold subNatNat ; simp
example: ofNat m + negSucc n = negSucc n + ofNat m := rfl
example: negSucc n + ofNat m = ofNat m + negSucc n := rfl

#check Nat.add_comm
protected theorem add_comm: a + b = b + a :=
  match a, b with
  | ofNat   a, ofNat   b => congrArg ofNat (Nat.add_comm a b)
  | ofNat   a, negSucc b => rfl
  | negSucc a, ofNat   b => rfl
  | negSucc a, negSucc b => congrArg (negSucc ∘ Nat.succ) (Nat.add_comm a b)

#check Nat.add_succ
theorem add_succ: a + n.succ = a + n + 1 := by
  match a with
  | ofNat   a => rfl
  | negSucc a =>
    calc subNatNat n.succ a.succ
      = subNatNat n a.succ + 1 := sorry

theorem subNatNat_succ_add_one: subNatNat n m.succ + 1 = subNatNat n m := by
  conv => left; unfold subNatNat
  match h: m.succ - n with
  | 0 =>
    simp; have m_lt_n := Nat.lt_of_succ_sub_eq_zero h
    calc ofNat (n - Nat.succ m) + 1
        = ofNat (n - m).pred + 1 := by rw [Nat.sub_succ]
      _ = ofNat (n - m).pred.succ := rfl
      _ = ofNat (n - m) :=
                  suffices (n - m).pred.succ = n - m from by rw [this]
                  Nat.succ_pred (Nat.sub_ne_zero_of_lt m_lt_n)
      _ = subNatNat n m :=
                  suffices m - n = 0 from by unfold subNatNat; rw [this]
                  Nat.sub_eq_zero_of_le (Nat.le_of_lt m_lt_n)
  | .succ k =>
    simp
    calc negSucc k + 1
        = subNatNat 1 k.succ := rfl
      _ = subNatNat 1 (m.succ - n) := by rw [h]
      _ = subNatNat n m :=
          by
            unfold subNatNat
            rw [Nat.succ_sub_sub_one, Nat.one_sub_succ]

#check Nat.succ_sub_succ
#check Nat.sub_succ
#check Nat.sub_add_eq
example: subNatNat n.succ m = subNatNat n m + 1 := by
  unfold subNatNat
  match h: m - n.succ with
  | 0 => simp; sorry
  | .succ k => sorry
  -- match m with
  -- | 0 => rw [subNatNat_zero, subNatNat_zero] ; rfl
  -- | .succ m =>
  --     unfold subNatNat
  --     rw [Nat.succ_sub_succ, Nat.succ_sub_succ]

#check Nat.add_assoc
protected theorem add_assoc: (a + b) + c = a + (b + c) := sorry

#check Nat.add_zero
@[simp] protected theorem add_zero: a + 0 = a := -- by cases a <;> rfl
  match a with
  | ofNat   a => rfl
  | negSucc a => rfl

#check Nat.zero_add
@[simp] protected theorem zero_add: 0 + a = a :=
  by simp [Int.add_comm]

#check Nat.sub_self
@[simp] protected theorem sub_self: a - a = 0 :=
  match a with
  | ofNat 0 => rfl
  | ofNat (.succ a) => subNatNat_self a.succ
  | negSucc a => subNatNat_self a.succ
@[simp] protected theorem add_neg: a + -a = 0 := Int.sub_self a
@[simp] protected theorem neg_add: -a + a = 0 := by simp [Int.add_comm]



@[simp] theorem negOfNat_zero: negOfNat 0 = 0 := rfl
-- @[simp] theorem negOfNat_succ: negOfNat n.succ = negSucc n := rfl

protected theorem mul_comm: a * b = b * a :=
  match a, b with
  | ofNat a, ofNat b => congrArg ofNat (Nat.mul_comm a b)
  | ofNat a, negSucc b => congrArg negOfNat (Nat.mul_comm a b.succ)
  | negSucc a, ofNat b => congrArg negOfNat (Nat.mul_comm a.succ b)
  | negSucc a, negSucc b => congrArg ofNat (Nat.mul_comm a.succ b.succ)

@[simp] protected theorem mul_zero: a * 0 = 0 := -- by cases a <;> rfl
  match a with
  | ofNat a => rfl
  | negSucc a => rfl
@[simp] theorem zero_mul: 0 * a = 0 :=
  by simp [Int.mul_comm]

theorem ofNat_mul_negOfNat: m * negOfNat n = negOfNat (m * n) :=
  match n with
  | 0 => rfl
  | .succ n => rfl
theorem negOfNat_mul_ofNat: negOfNat m * n = negOfNat (m * n) :=
  by rw [Int.mul_comm, Nat.mul_comm, ofNat_mul_negOfNat]
theorem negOfNat_mul_negSucc: negOfNat m * negSucc n = ofNat (m * n.succ) :=
  match m with
  | 0 => by simp
  | .succ m => rfl
theorem negSucc_mul_negOfNat: negSucc m * negOfNat n = ofNat (m.succ * n) :=
  by rw [Int.mul_comm, Nat.mul_comm, negOfNat_mul_negSucc]

protected theorem mul_assoc: (a * b) * c = a * (b * c) :=
  match a, b, c with
  | ofNat   a, ofNat   b, ofNat   c => congrArg ofNat (Nat.mul_assoc a b c)
  | ofNat   a, ofNat   b, negSucc c =>
    show negOfNat ((a * b) * c.succ) = a * negOfNat (b * c.succ)
    from by rw [Nat.mul_assoc, ofNat_mul_negOfNat]
  | ofNat   a, negSucc b, ofNat   c =>
    show negOfNat (a * b.succ) * c = a * negOfNat (b.succ * c)
    from by rw [negOfNat_mul_ofNat, Nat.mul_assoc, ofNat_mul_negOfNat]
  | ofNat   a, negSucc b, negSucc c =>
    show negOfNat (a * b.succ) * negSucc c = ofNat (a * (b.succ * c.succ))
    from by rw [negOfNat_mul_negSucc, Nat.mul_assoc]
  | negSucc a, ofNat   b, ofNat   c =>
    show negOfNat (a.succ * b) * c = negOfNat (a.succ * (b * c))
    from by rw [negOfNat_mul_ofNat, Nat.mul_assoc]
  | negSucc a, ofNat   b, negSucc c =>
    show negOfNat (a.succ * b) * negSucc c = negSucc a * negOfNat (b * c.succ)
    from by rw [negOfNat_mul_negSucc, Nat.mul_assoc, negSucc_mul_negOfNat]
  | negSucc a, negSucc b, ofNat   c =>
    show ofNat (a.succ * b.succ * c) = negSucc a * negOfNat (b.succ * c)
    from by rw [Nat.mul_assoc, negSucc_mul_negOfNat]
  | negSucc a, negSucc b, negSucc c =>
    congrArg negOfNat (Nat.mul_assoc a.succ b.succ c.succ)

#check Nat.mul_one
@[simp] protected theorem mul_one: a * 1 = a :=
  match a with
  | ofNat a => congrArg ofNat (Nat.mul_one a)
  | negSucc a => congrArg negOfNat (Nat.mul_one a.succ)
@[simp] protected theorem one_mul: 1 * a = a :=
  by simp [Int.mul_comm]

protected theorem mul_add: a * (b + c) = a * b + a * c :=
  match a, b, c with
  | ofNat   a, ofNat   b, ofNat   c => congrArg ofNat (Nat.mul_add a b c)
  | ofNat   a, ofNat   b, negSucc c => _
  | ofNat   a, negSucc b, ofNat   c => _
  | ofNat   a, negSucc b, negSucc c => _
  | negSucc a, ofNat   b, ofNat   c => _
  | negSucc a, ofNat   b, negSucc c => _
  | negSucc a, negSucc b, ofNat   c => _
  | negSucc a, negSucc b, negSucc c =>
    congrArg ofNat (Nat.mul_add a.succ b.succ c.succ)
protected theorem add_mul: (a + b) * c = a * c + b * c :=
  by simp [Int.mul_add, Int.mul_comm]

end Int
