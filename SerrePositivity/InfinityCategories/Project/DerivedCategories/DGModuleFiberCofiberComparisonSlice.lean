module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFiberCofiberComparisonJoin
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberCofiberComparisonSlice
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.RebaseCocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness

/-! # 標準 fiber の実際の coslice 比較辺

概要：標準 cofiber 余錐から元の fiber 余錐への辺を coslice 内に構成する。
方針：二つの span を同定し、比較 join 写像を curry する。
規約：両端の四角形を厳密に保持する。使われ方：β3 の標準 fiber の押し出し性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable {M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}

/-- 二つの標準四角形は同じ span を持つ。 -/
lemma dgModuleFiberCofiberComparison_span (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f) := by
  apply SSet.horn₂₀.isPushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_bottom]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_bottom A D f).symm
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_left]
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_left A D f).symm

/-- 元の fiber 余錐を標準 cofiber の span 上で読む。 -/
def dgModuleFiberCofiberTargetCocone (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone (dgModuleFiberCofiberComparison_span A D f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D f))

/-- 比較 join 写像は span を固定する。 -/
lemma dgModuleFiberCofiberComparisonJoin_fixed (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin A D f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)) := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (SSet.horn 2 0 : SSet.{max (u + 1) v}) Δ[0] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (SSet.horn 2 0 : SSet.{max (u + 1) v})) (SSet.stdSimplex.δ (1 : Fin 2))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin A D f := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin_face_one]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)).property

/-- 標準 cofiber 余錐から元の fiber 余錐への実際の coslice 辺。 -/
def dgModuleFiberCofiberComparisonSliceEdge (f : M ⟶ N) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f)))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeCocone A D (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberProjection A D f))
      (dgModuleFiberCofiberTargetCocone A D f) where
  edge := SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin A D f)
      (dgModuleFiberCofiberComparisonJoin_fixed A D f))
  src_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_vertex_of_join _ _ 1 _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin_face_one A D f)
  tgt_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceUnderCurry_vertex_of_join _ _ 0 _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCofiberComparisonJoin_face_zero A D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
