module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleCofiberFiberComparisonJoin
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CofiberFiberComparisonSlice
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.RebaseCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness

/-! # 標準 cofiber 錐から標準 fiber 錐への実際の辺

概要：貼り合わせた join 写像を curry し、同じ cospan 上の slice の比較辺を作る。
方針：二つの四角形の cospan を同定し、join の端点の等式から始点と終点を確認する。
規約：普遍性による選択に依存しない。使われ方：β3 の極限性の移送。
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

/-- 二つの標準四角形は同じ cospan を持つ。 -/
lemma dgModuleCofiberFiberComparison_cospan (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f) := by
  apply SSet.horn₂₂.isPushout.hom_ext
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_rightEdge,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_right]
  · simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan, ← Category.assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.cospanSquareBoundary_topEdge,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare_top, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare_top]

/-- 元の cofiber 錐を標準 fiber の cospan 上で読む。 -/
def dgModuleCofiberFiberSourceCone (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone (dgModuleCofiberFiberComparison_cospan A D f) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleConeSquare A D f))

/-- 比較 join 写像は cospan を固定する。 -/
lemma dgModuleCofiberFiberComparisonJoin_fixed (f : M ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] : SSet) (SSet.horn 2 2) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin A D f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f)) := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet) (SSet.horn 2 2) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.δ (0 : Fin 2)) (𝟙 (SSet.horn 2 2 : SSet))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin A D f := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp]
    _ = _ := by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin_face_zero]
      exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D (moduleConeInr A D f)).property

/-- 元の錐から標準 fiber 錐への、明示的な slice 比較辺。 -/
def dgModuleCofiberFiberComparisonSliceEdge (f : M ⟶ N) :
    SSet.Truncated.Edge (X := (SSet.truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberSquare A D (moduleConeInr A D f)))))
      (dgModuleCofiberFiberSourceCone A D f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFiberCone A D (moduleConeInr A D f)) where
  edge := SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin A D f)
      (dgModuleCofiberFiberComparisonJoin_fixed A D f))
  src_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCurry_vertex_of_join _ _ 1 _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin_face_one A D
    f)
  tgt_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceOverCurry_vertex_of_join _ _ 0 _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCofiberFiberComparisonJoin_face_zero A
    D f)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
