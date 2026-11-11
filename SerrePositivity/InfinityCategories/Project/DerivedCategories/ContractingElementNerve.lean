module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.EdgeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryBridge

/-! # 収縮元と dg nerve の恒等辺の零ホモトピー

概要：d h = id となる次数 −1 元から、恒等辺と零辺の実際の左ホモトピーを得る。
方針：dg nerve の二単体の微分方程式を辺ホモトピーの判定に適用する。
規約：任意の dg 圏でよい。使われ方：β3 の商で殺す対象の収縮。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 収縮元を持つ dg 対象の恒等辺は、零辺と左ホモトピック。 -/
lemma dgNerve_contractingElement_id_homotopic_zero (x : D)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) :
    Truncated.HomotopicL
      (Truncated.Edge.id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) 0) := by
  apply (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.homotopicL_iff_exists _ _).2
  refine ⟨h, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeCycle_edgeOfCycle]
  change (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val - 0
  rw [sub_zero]
  exact dh

/-- 収縮元を持つ対象の恒等射は、通常の h で零辺の類に一致する。 -/
lemma dgNerve_contractingElement_id_eq_zeroEdge (x : D)
    (h : _root_.SerrePositivity.DifferentialGraded.GradedHom A x x (-1))
    (dh : (_root_.SerrePositivity.DifferentialGraded.homObject A D x x).d (-1) 0 h = (_root_.SerrePositivity.DifferentialGraded.unitElement A x).val) :
    𝟙 (Truncated.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) :
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A D).HomotopyCategory) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) 0) := by
  exact (Truncated.HomotopyCategory.homMk_id _).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopic_path_eq _ (dgNerve_contractingElement_id_homotopic_zero x h dh))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
