#check_failure Inv
class HInv (α: Sort u) (β: outParam (Sort v)) where
  hInv : α → β
postfix:arg "⁻¹" => HInv.hInv
