set_option autoImplicit false

inductive I | zero | one
@[default_instance] instance: OfNat I (nat_lit 0) where ofNat := I.zero
@[default_instance] instance: OfNat I (nat_lit 1) where ofNat := I.one

inductive Path.{u} {A: I → Type u} (a: A 0) (b: A 1): Type u
  | abst (α: (i: I) → A i): Path a b

#check CoeFun
protected instance Path.abstFun.{u} {A: I → Type u} (a: A 0) (b: A 1):
  CoeFun (Path a b) (fun _ => (i: I) → A i)
where
  coe _ | 0 => a | 1 => b

section
  universe u
  variable {A: I → Type u} (a: A 0) (b: A 1) (p: Path a b)

  example (r: I): A r := p r -- let .abst α := p; α r
  example: p 0 = a := rfl
  example: p 1 = b := rfl
end

abbrev Loop.{u} {A: Type u} (a b: A) := @Path (fun _ => A) a b
def refl.{u} {A: Type u} (a: A): Loop a a := .abst (fun _ => a)