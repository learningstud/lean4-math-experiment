import Halmos.Nat

#check Nat.mod
#check Nat.decLe

protected def ℕ.mod (x y: ℕ): ℕ :=
  if 0 < y ∧ y ≤ x then ℕ.mod (x.sub y) y else x
-- decreasing_by apply div_rec_lemma; assumption

protected def mod_core (y: ℕ): ℕ → ℕ → ℕ
  | 0, x => x
  | (fuel+1) x := if h : 0 < y ∧ y ≤ x then mod_core fuel (x - y) else x

protected def mod (x y : ℕ) : ℕ :=
nat.mod_core y x x

def ℕ.gcd: ℕ → ℕ → ℕ
  | 0, n => n
  | m⁺, n => have n % succ m < succ m, from mod_lt _ $ succ_pos _,
                gcd (n % succ m) (succ m)
