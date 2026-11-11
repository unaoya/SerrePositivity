module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalBoundaryDiagramExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFiberTranspose
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.PastingRightCocone

/-!
概要：相対 join 上の関手の制限の正次元の境界充填。
方針：境界の関手を転置し、最初の頂点の fiber の余極限性から大域図式を延長して戻す。
規約：境界の他の頂点に普遍性は要求しない。
使われ方：普遍な相対 join 図式から元の図式への制限の写像空間の制御。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：最初の境界図式が各 fiber で普遍なら、相対 join 上の関手の境界を全体へ延長できる。
方針：局所の余錐の族の境界充填と大域的な相対組み立てを転置で関手の族へ戻す。
規約：境界と元の図式を厳密に固定する。
使われ方：普遍図式の制限射の始点境界充填を証明する。 -/
lemma exists_kanRelativeJoin_functor_boundary_extension {K C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj D)
    (ha : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D = (boundary (n + 1)).ι ≫ d)
    (hfirst : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm
        (a.app (Opposite.op ⦋0⦌)
          ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩)))) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧ f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D = d := by
  have hFU : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose ha
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left] at h
    exact h.symm
  have hlocal : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a)).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩) := by
    intro c
    exact (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.isColimitCone_iff_of_val_eq _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_transpose_familyAt_val p c a _)).2 (hfirst c)
  obtain ⟨H, hHF, hHA, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanGlobalBoundary_diagram_extension p n
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose d) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a) hFU hlocal
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose H, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, hHA, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_transpose]
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left, hHF, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_transpose]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
