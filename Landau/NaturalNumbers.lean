import Geometry.Logic



section Axioms

/-- The natural numbers -/
axiom N : Type

/-- The element 1 -/
axiom axm1 : N
@[default_instance]
noncomputable instance : OfNat N (nat_lit 1) where ofNat := axm1

/-- The successor function -/
@[match_pattern] axiom axm2 : N → N
postfix:arg "′" => axm2
theorem N.succ_congr_arg {x y : N} : x = y → x′ = y′ := congrArg (· ′)

/-- 1 cannot be a successor -/
axiom axm3 : ∀ {x : N}, x′ ≠ 1

/-- The successor function is injective -/
axiom axm4 : ∀ {x y : N}, x′ = y′ → x = y

/-- The induction principle -/
axiom axm5 : ∀ {p : N → Prop}, p 1 → (∀ x : N, p x → p x′) → ∀ x : N, p x

end Axioms


def simplyAbsurd {C : Sort u} {a : α} (ne : a ≠ a) : C :=
  absurd rfl ne
theorem N.one_or_succ : ∀ x, x = 1 ∨ ∃ u, x = u′ :=
  axm5 (.inl rfl) fun x ih => ih.elim
    (fun _ => .inr ⟨x, rfl⟩)
    fun ⟨u, h⟩ => .inr ⟨u′, succ_congr_arg h⟩
theorem N.one_or_ne_one (x : N) : x = 1 ∨ x ≠ 1 :=
  (one_or_succ x).elim .inl fun ⟨_, h⟩ => .inr (h ▸ axm3)
example : ∀ x, x ≠ 1 → ∃ u, x = u′ :=
  axm5 simplyAbsurd fun x ih _ => x.one_or_ne_one.elim
    (fun _  => ⟨x, rfl⟩)
    (fun h  => let ⟨a, p⟩ := ih h ; ⟨a′, N.succ_congr_arg p⟩)
section
variable (α : Sort u)
#check PProd α Prop
end

section Addition

theorem thm1 : x ≠ y → x′ ≠ y′ :=
  fun h h' => h (axm4 h')
theorem thm2 : ∀ x, x′ ≠ x :=
  axm5 axm3 fun _ => thm1
theorem thm3 : ∀ x, x ≠ 1 → ∃! u, x = u′ :=
  axm5 simplyAbsurd fun x ih _ => x.one_or_ne_one.elim
    (fun h => ⟨x, rfl, fun y h' => (axm4 h').symm⟩)
    fun h => let ⟨a, p, q⟩ := ih h ; ⟨a′, N.succ_congr_arg p, fun y r =>
      y.one_or_succ.elim (fun h' => absurd (axm4 (h' ▸ r)) h)
      fun ⟨u, h⟩ => q u (axm4 r ▸ h) ▸ h
    ⟩

axiom add : N → N → N
noncomputable instance : Add N where add := add
example : ∃! f : N → N → N, ∀ x, f x 1 = x′ ∧ ∀ y, f x y′ = (f x y)′ :=
  ⟨add, sorry, fun f h => _⟩
example (α β : Type u) (f g : α → β) : (∀ a : α, f a = g a ) → f = g :=
  funext
example : ∃ f : N → N → N, ∀ x, f x 1 = x′ ∧ ∀ y, f x y′ = (f x y)′ :=
  Exists.intro add (axm5 _ _)

end Addition
