module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.GlobalRelativeBoundaryExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeJoinFiberTranspose

/-!
概要：元の図式と U による全図式を固定する相対 join 関手の境界延長。
方針：関手の族を転置し、三つの指定を保つ大域境界延長を適用する。
規約：境界の最初の頂点の局所 U 余極限性だけを要求する。
使われ方：相対制限の始点境界充填と写像空間の制限定理。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：標的の全関手も固定して相対 join 上の関手の境界を延長できる。
方針：局所余錐の頂点表示を同定して転置し、相対内部 Hom 上で大域的に組み立てる。
規約：元の図式、全境界、標的の全図式を厳密に保つ。
使われ方：普遍な相対図式の制限の正次元の境界充填。 -/
lemma exists_kanRelativeJoin_functor_relative_boundary_extension {K C D E : SSet.{u}}
    [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (p : K ⟶ C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (U : D ⟶ E) (hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting U)
    (n : ℕ)
    (a : (boundary (n + 1) : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D)
    (d : (Δ[n + 1] : SSet.{u}) ⟶ (ihom K).obj D)
    (g : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj E)
    (hdg : d ≫ (ihom K).map U = g ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app E)
    (had : a ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D = (boundary (n + 1)).ι ≫ d)
    (hag : a ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).map U = (boundary (n + 1)).ι ≫ g)
    (hfirst : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C)) D).symm
        (a.app (Opposite.op ⦋0⦌)
          ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩)))) :
    ∃ f : (Δ[n + 1] : SSet.{u}) ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).obj D,
      (boundary (n + 1)).ι ≫ f = a ∧
        f ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C))).app D = d ∧
          f ≫ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoin p (𝟙 C))).map U = g := by
  have hFA : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose d ≫ (pre (boundary (n + 1)).ι).app D =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose had
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left] at h
    exact h.symm
  have hFG : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose d ≫ (ihom (Δ[n + 1] : SSet.{u})).map U =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInl p (𝟙 C) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose g := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose hdg
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorTranspose_postcomp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right] at h
    exact h
  have hAG : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a ≫ (ihom (boundary (n + 1) : SSet.{u})).map U =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose g ≫ (pre (boundary (n + 1)).ι).app E := by
    have h := congrArg _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose hag
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorTranspose_postcomp, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left] at h
    exact h
  have hlocal : ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a)).val)
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩) := by
    intro c
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone_transpose_familyAt_val p c a
      ⟨stdSimplex.obj₀Equiv.symm (0 : Fin (n + 2)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanIsRelativeColimitCone_congr U ?_ _ _ hv).2 (hfirst c)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyAt _ _).property.symm.trans
      ((congrArg (fun f ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p c) (Δ[0] : SSet.{u}) ≫ f) hv).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeJoinFiberCocone p c _).property)
  let sj := Functor.PullbackObjObj.ofHasPullback internalHom (boundary (n + 1)).ι U
  obtain ⟨H, hHF, hHA, hHG⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.exists_kanGlobalRelativeBoundary_diagram_extension p U hU n sj
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose d) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose a) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose g) hFA hFG hAG hlocal
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose H, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_right, hHA, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_transpose]
  · rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_pre_left, hHF, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_transpose]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorTranspose_postcomp, hHG, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose_transpose]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
