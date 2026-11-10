module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ParameterRightKan
public import SerrePositivity.InfinityCategories.Core.FunctorPointwiseLimitCriterion
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：右 ∞ 随伴による任意の coherent 図式の指定極限錐の保存を証明する。
方針：標準 Hom の式と、相対境界充填の判定を使用する。
規約：元の対象・射・端点の同一視を保持する。使われ方：一般 coherent 極限保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 指定した制限の相対終点は、同じ標準単位を持つ右随伴の後合成で保たれる。 -/
lemma terminalBoundaryLifting_pre_postcomp_of_unitCondition {K L X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (δ : K ⟶ L) [Mono δ]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitMappingSpaceCondition η) (H : L ⟶ Y)
    (hc : TerminalBoundaryLifting ((pre δ).app Y) (functorVertex H)) :
    TerminalBoundaryLifting ((pre δ).app X) (functorVertex (H ≫ G)) := by
  have hp : ∀ (A : SSet.{u}) [Quasicategory A], RightKanHomUniversal
      (F := uncurry (SSet.const (functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))
      (F₀ := (δ ▷ A) ≫ uncurry (SSet.const (functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))
      (δ ▷ A) (𝟙 (HomotopyCategory.mk (functorVertex
        ((δ ▷ A) ≫ uncurry (SSet.const (functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X))))) := by
    intro A _
    have hu := parameterRightKanIdentity_of_terminalBoundary δ H hc A
    have hv := rightKanIdentity_postcomp (δ ▷ A) η hη
      (uncurry (SSet.const (functorVertex H) : A ⟶ (ihom L).obj Y)) hu
    have he : uncurry (SSet.const (functorVertex H) : A ⟶ (ihom L).obj Y) ≫ G =
        uncurry (SSet.const (functorVertex (H ≫ G)) : A ⟶ (ihom L).obj X) := by
      rw [uncurry_const_functorVertex, uncurry_const_functorVertex]
      rfl
    let P (M : L ⊗ A ⟶ X) : Prop := RightKanHomUniversal
      (F := M) (F₀ := (δ ▷ A) ≫ M) (δ ▷ A)
      (𝟙 (HomotopyCategory.mk (functorVertex ((δ ▷ A) ≫ M))))
    exact (congrArg P he).mp hv
  apply terminalBoundaryLifting_of_parameterHom_bijective ((pre δ).app X)
    (functorVertex (H ≫ G))
  intro A _ y
  obtain ⟨T, rfl⟩ := (functorVertexEquiv L X).surjective y
  exact constantHom_precomp_bijective_of_parameterRightKan δ (H ≫ G) hp A T

/-- 右 ∞ 随伴は、任意の coherent 図式の元の指定極限錐を保存する。 -/
@[kerodon 02KE]
lemma mapJoinCone_isLimit_of_adjunction {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) {p : K ⟶ Y} (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone G c) := by
  apply isLimitCone_of_terminalBoundaryLifting_coneRestriction
  exact terminalBoundaryLifting_pre_postcomp_of_unitCondition (joinInr (Δ[0] : SSet.{u}) K)
    a.unitHom a.unitMappingSpaceCondition c.val
    (terminalBoundaryLifting_coneRestriction_of_isLimitCone c hc)

/-- 右 ∞ 随伴の後合成は、元の図式の極限の存在を保つ。 -/
lemma hasLimit_postcomp_of_adjunction {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (a : QCatAdjunction F G) (p : K ⟶ Y) (hp : HasLimit p) : HasLimit (p ≫ G) := by
  obtain ⟨c, hc⟩ := hp
  exact ⟨mapJoinCone G c, mapJoinCone_isLimit_of_adjunction a c hc⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
