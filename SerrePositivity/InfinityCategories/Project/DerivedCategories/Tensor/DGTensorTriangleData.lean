module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorClosedCycles
/-!
概要：二つの実三角形から、三閉辺と実比較 cochain を保つ tensor 三角形を構成する。
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
def dgTensorTriangle (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R B) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TriangleData R (_root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C) where
  obj i := (s.obj i, t.obj i)
  f01 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorZeroCycle R B C s.f01 t.f01
  f12 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorZeroCycle R B C s.f12 t.f12
  f02 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorZeroCycle R B C s.f02 t.f02
  homotopy := dgTensorElement R s.homotopy
      (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0)) (by decide) +
    dgTensorElement R s.f02.val t.homotopy (by decide)
  differential_homotopy := by
    have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorBoundary R B C (s.obj 0, t.obj 0) (s.obj 2, t.obj 2)
      s.f02.val (compose R s.f12.val s.f01.val (by decide : (0 : ℤ) + 0 = 0))
      t.f02.val (compose R t.f12.val t.f01.val (by decide : (0 : ℤ) + 0 = 0))
      s.homotopy t.homotopy s.f02.property (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTriangle_composite_closed R C t)
      s.differential_homotopy t.differential_homotopy
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorZeroCycle, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_composeZero] using! h
end SerrePositivity.InfinityCategories.Project.DerivedCategories
