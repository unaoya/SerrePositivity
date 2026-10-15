module
public import SerrePositivity.DifferentialGraded.Module.LeftAction

/-! # opposite表示の作用と元の左右作用 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

lemma leftToRightOpposite_action (N : LeftModule A D) {x y : D} {p r n : ℤ}
    (f : GradedHom A x y p) (v : (N.obj x).X r) (hn : r + p = n) :
    moduleAction A N.toRightOpposite (x := op (op x)) (y := op (op y)) f v hn =
      leftAction A N f v hn := by
  change (((𝟙 _ ≫ N.map x y).f p f).v r n hn) v = _
  rw [Category.id_comp]
  rfl

lemma rightToLeft_action (M : RightModule A D) {x y : Dᵒᵖ} {p r n : ℤ}
    (f : GradedHom A x y p) (v : (M.obj x).X r) (hn : r + p = n) :
    leftAction A M.toFunctor f v hn = moduleAction A M f v hn := rfl

end SerrePositivity.DifferentialGraded
