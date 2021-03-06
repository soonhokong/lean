open nat
namespace foo
section
  parameter (X : Type₁)
  definition A {n : ℕ} : Type₁ := X
  variable {n : ℕ}
  set_option pp.implicit true
  check @A n
  set_option pp.full_names true
  check @foo.A X n
  check @A n

  set_option pp.full_names false
  check @foo.A X n
  check @A n
end
end foo
