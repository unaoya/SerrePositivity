module
public import SerrePositivity.DifferentialGraded.Tensor.Elements

/-! # 右次数零のbalanced関係 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
lemma leftAction_heq (N : LeftModule A D) {x y : D} {p r n n' : ℤ}
    (f : GradedHom A x y p) (t : (N.obj x).X r)
    (hn : r + p = n) (hn' : r + p = n') :
    HEq (DifferentialGraded.leftAction A N f t hn)
      (DifferentialGraded.leftAction A N f t hn') := by
  have h : n = n' := hn.symm.trans hn'
  cases h
  rfl

lemma element_balanced_zero (M : RightModule A D) (N : LeftModule A D) (x y : D)
    {r p : ℤ} (m : (M.obj (op y)).X r) (f : GradedHom A x y p)
    (t : (N.obj x).X 0) :
    (r * p).negOnePow • element A D M N x (moduleAction A M f m rfl) t
      (add_zero (r + p)) =
    element A D M N y m
      (SerrePositivity.DifferentialGraded.leftAction A N f t (zero_add p)) rfl := by
  convert (element_balanced A D M N x y m f t (add_zero (r + p))) using 1
  congr 1
  · exact (add_zero p).symm
  · exact leftAction_heq A D N f t _ _
  · exact proof_irrel_heq _ _

end SerrePositivity.DifferentialGraded.BalancedTensor
