module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Triangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Algebra
/-!
概要：二つの閉射の tensor と同じ実零次数合成を照合する。
方針：元の境界式をそのまま同じ二原始元の tensor 微分式へ渡す。
規約：元の入力の Small 性・Hom の平坦性は不要。使われ方：実 dg nerve の二単体。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [DGCategory R C]
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
def dgTensorZeroCycle {x y : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C}
    (f : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject R B x.1 y.1)) (g : _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject R C x.2 y.2)) :
    _root_.SerrePositivity.DifferentialGraded.zeroCycles (homObject R (DGTensorCategory R B C) x y) :=
  ⟨dgTensorElement R f.val g.val (by decide),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_closed R B C f.val g.val f.property g.property⟩
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
lemma dgTensorElement_composeZero {x y z : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C}
    (f₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.1 y.1 0) (f₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R x.2 y.2 0)
    (g₁ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.1 z.1 0) (g₂ : _root_.SerrePositivity.DifferentialGraded.GradedHom R y.2 z.2 0) :
    _root_.SerrePositivity.DifferentialGraded.compose R (dgTensorElement R g₁ g₂ (by decide : (0 : ℤ) + 0 = 0))
      (dgTensorElement R f₁ f₂ (by decide : (0 : ℤ) + 0 = 0)) (by decide : (0 : ℤ) + 0 = 0) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R (compose R g₁ f₁ (by decide : (0 : ℤ) + 0 = 0))
      (compose R g₂ f₂ (by decide : (0 : ℤ) + 0 = 0)) (by decide : (0 : ℤ) + 0 = 0) := by
  simpa only [_root_.SerrePositivity.DifferentialGraded.compose, mul_zero, Int.negOnePow_zero, one_smul] using!
    dgTensor_forward R f₁ f₂ g₁ g₂ (show (0 : ℤ) + 0 + (0 + 0) = 0 by decide)
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
lemma dgTriangle_composite_closed (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R C) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R C (t.obj 0) (t.obj 2)).d 0 1
      (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0)) = 0 := by
  change _root_.SerrePositivity.DifferentialGraded.differential R (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0)) = 0
  rw [_root_.SerrePositivity.DifferentialGraded.differential_compose, show differential R t.f12.val = 0 from t.f12.property,
    show differential R t.f01.val = 0 from t.f01.property, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero,
    smul_zero, add_zero]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
