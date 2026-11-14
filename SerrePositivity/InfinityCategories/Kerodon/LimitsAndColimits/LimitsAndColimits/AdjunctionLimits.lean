module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.ParameterRightKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitCriterion
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：右 ∞ 随伴による任意の coherent 図式の指定極限錐の保存を証明する。
方針：標準 Hom の式と、相対境界充填の判定を使用する。
規約：元の対象・射・端点の同一視を保持する。使われ方：一般 coherent 極限保存。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section

/-- 指定した制限の相対終点は、同じ標準単位を持つ右随伴の後合成で保たれる。 -/
lemma terminalBoundaryLifting_pre_postcomp_of_unitCondition {K L X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ L) [Mono δ]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (hη : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition η) (H : L ⟶ Y)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre δ).app Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting ((pre δ).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G)) := by
  have hp : ∀ (A : SSet.{u}) [Quasicategory A], _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal
      (F := uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))
      (F₀ := (δ ▷ A) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))
      (δ ▷ A) (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        ((δ ▷ A) ≫ uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))))) := by
    intro A _
    have hu := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterRightKanIdentity_of_terminalBoundary δ H hc A
    have hv := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.rightKanIdentity_postcomp (δ ▷ A) η hη
      (uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : A ⟶ (ihom L).obj Y)) hu
    have he : uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex H) : A ⟶ (ihom L).obj Y) ≫ G =
        uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X) := by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
      rfl
    let P (M : L ⊗ A ⟶ X) : Prop := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanHomUniversal
      (F := M) (F₀ := (δ ▷ A) ≫ M) (δ ▷ A)
      (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((δ ▷ A) ≫ M))))
    exact (congrArg P he).mp hv
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.terminalBoundaryLifting_of_parameterHom_bijective ((pre δ).app X)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (H ≫ G))
  intro A _ y
  obtain ⟨T, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv L X).surjective y
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.constantHom_precomp_bijective_of_parameterRightKan δ (H ≫ G) hp A T

/-- 右 ∞ 随伴は、任意の coherent 図式の元の指定極限錐を保存する。 -/
@[kerodon 02KE]
lemma mapJoinCone_isLimit_of_adjunction {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) {p : K ⟶ Y} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone G c) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_of_terminalBoundaryLifting_coneRestriction
  exact terminalBoundaryLifting_pre_postcomp_of_unitCondition (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) K)
    a.unitHom a.unitMappingSpaceCondition c.val
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc)

/-- 右 ∞ 随伴の後合成は、元の図式の極限の存在を保つ。 -/
lemma hasLimit_postcomp_of_adjunction {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (p : K ⟶ Y) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (p ≫ G) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone G c, mapJoinCone_isLimit_of_adjunction a c hc⟩

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.3.5"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.mapJoinCone_isLimit_of_adjunction
