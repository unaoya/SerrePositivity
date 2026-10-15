module
public import SerrePositivity.DifferentialGraded.Module.LeftAction
public import SerrePositivity.DifferentialGraded.Module.Representable

/-! # 共変representable左dg加群 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- xにおける値がD(z,x)である共変representable。 -/
def leftRepresentable (z : D) : LeftModule A D :=
  LeftModule.ofRightOpposite (representable A (op z))

lemma leftRepresentable_action (z x y : D) {p q n : ℤ}
    (f : GradedHom A x y p) (h : GradedHom A z x q) (hn : q + p = n) :
    leftAction A (leftRepresentable A z) f h hn =
      (p * q).negOnePow • forward A h f hn := by
  change (((𝟙 _ ≫ representableMap A (op z) (op (op x)) (op (op y))).f p f).v q n hn h) = _
  simp only [Category.id_comp]
  change forward A (D := Dᵒᵖ) (x := op y) (y := op x) (z := op z) f h (by omega) = _
  exact opposite_forward A D (op y) (op x) (op z) p q n (by omega) f h

end SerrePositivity.DifferentialGraded
