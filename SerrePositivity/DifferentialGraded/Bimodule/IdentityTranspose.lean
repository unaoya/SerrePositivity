module
public import SerrePositivity.DifferentialGraded.Bimodule.Identity
public import SerrePositivity.DifferentialGraded.Bimodule.Transpose
public import SerrePositivity.DifferentialGraded.Module.LeftHomElements

/-! # 対角bimoduleの転置作用の成分 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.Bimodule
open CategoryTheory Opposite CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma diagonal_transpose_element {b b' : Dᵒᵖ} (x : D) {p s n : ℤ}
    (f : GradedHom A b b' p) (h : GradedHom A b.unop x s) (hn : s + p = n) :
    (((leftModuleHomπ A D ((diagonal A D).leftAt b.unop)
      ((diagonal A D).leftAt b'.unop) x).f p
        (((diagonal A D).transposeHom b b').f p f)).v s n hn) h =
    forward A (D := D) (x := b'.unop) (y := b.unop) (z := x) f h (by omega) := by
  have hp := congrArg (fun t => t.f p f) ((diagonal A D).transposeHom_π b b' x)
  change (leftModuleHomπ A D ((diagonal A D).leftAt b.unop)
      ((diagonal A D).leftAt b'.unop) x).f p
        (((diagonal A D).transposeHom b b').f p f) =
    ((representable A x).map b b').f p f at hp
  rw [hp]
  exact representableMap_apply A x b b' p s n hn f h

end SerrePositivity.DifferentialGraded.Bimodule
