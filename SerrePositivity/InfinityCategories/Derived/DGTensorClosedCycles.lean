module
public import SerrePositivity.InfinityCategories.Derived.DGTensorBoundary
public import SerrePositivity.InfinityCategories.DGNerve.Triangle
public import SerrePositivity.InfinityCategories.DGNerve.Algebra
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory HomologicalComplex DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
def dgTensorZeroCycle {x y : DGTensorCategory R B C}
    (f : zeroCycles (homObject R B x.1 y.1)) (g : zeroCycles (homObject R C x.2 y.2)) :
    zeroCycles (homObject R (DGTensorCategory R B C) x y) :=
  ⟨dgTensorElement R f.val g.val (by decide),
    dgTensorElement_closed R B C f.val g.val f.property g.property⟩
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
lemma dgTensorElement_composeZero {x y z : DGTensorCategory R B C}
    (f₁ : GradedHom R x.1 y.1 0) (f₂ : GradedHom R x.2 y.2 0)
    (g₁ : GradedHom R y.1 z.1 0) (g₂ : GradedHom R y.2 z.2 0) :
    compose R (dgTensorElement R g₁ g₂ (by decide : (0 : ℤ) + 0 = 0))
      (dgTensorElement R f₁ f₂ (by decide : (0 : ℤ) + 0 = 0)) (by decide : (0 : ℤ) + 0 = 0) =
    dgTensorElement R (compose R g₁ f₁ (by decide : (0 : ℤ) + 0 = 0))
      (compose R g₂ f₂ (by decide : (0 : ℤ) + 0 = 0)) (by decide : (0 : ℤ) + 0 = 0) := by
  simpa only [compose, mul_zero, Int.negOnePow_zero, one_smul] using!
    dgTensor_forward R f₁ f₂ g₁ g₂ (show (0 : ℤ) + 0 + (0 + 0) = 0 by decide)
/-- 同じ実閉辺・合成・比較 cochain を保持する tensor 三角形の計算。 -/
lemma dgTriangle_composite_closed (t : TriangleData R C) :
    (homObject R C (t.obj 0) (t.obj 2)).d 0 1
      (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0)) = 0 := by
  change differential R (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0)) = 0
  rw [differential_compose, show differential R t.f12.val = 0 from t.f12.property,
    show differential R t.f01.val = 0 from t.f01.property, zero_compose, compose_zero,
    smul_zero, add_zero]
end SerrePositivity.InfinityCategories
