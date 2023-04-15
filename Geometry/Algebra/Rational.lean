structure ℚ where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat ℚ n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString ℚ where
  toString x := s!"{x.num}/{x.den}"

#eval (2 : ℚ)

def mulDen (x y : ℚ) (numF : ℚ → ℚ → Int) : ℚ :=
  {
    num := numF x y
    den := x.den * y.den
    inv := sorry
  }

instance : Add ℚ where
  add x y := mulDen x y fun x y => x.num * y.den + y.num * x.den
instance : Neg ℚ where
  neg x := { x with num := -x.num }
instance : Sub ℚ where
  sub x y := x + (-y)
instance : Mul ℚ where
  mul x y := mulDen x y fun x y => x.num * y.num
  
-- example {x y : Int} : x ≠ 0 ∧ y ≠ 0 → x * y ≠ 0 := by
--   intro ⟨hx, hy⟩ hxy
