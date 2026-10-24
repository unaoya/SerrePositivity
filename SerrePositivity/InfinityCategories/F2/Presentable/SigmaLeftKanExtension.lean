module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaElementsLeftKanModel
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSiftedGeneration
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentRestrictionColimit
public import SerrePositivity.InfinityCategories.F2.Ind.FullyFaithfulKanUnit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCommaCoconeColimit

/-!
概要：小さい sifted 余極限を持つ標的へ、元の P_Σ Yoneda に沿う左 Kan 延長を構成。
方針：同じ小さい元の圏上の局所余極限を構成し、元の比較同値と全局所存在定理を使う。
規約：同じ元の図式と指定単位を保持。延長の sifted 保存性は別工程。
使われ方：P_Σ の全関手 ∞ 圏の普遍性の、延長存在への入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {D : SSet.{u + 1}} [Quasicategory D]

/-- 全ての元の P_Σ Yoneda 局所図式は、小さい sifted 余極限の存在で余極限を持つ。 -/
lemma sigmaLeftKanDiagram_hasColimit
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hD : HasSmallSiftedColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    HasColimit (leftKanDiagram (sigmaYonedaInfinityMap C) F₀ v) := by
  have : IsSiftedInfinity (smallRightUnstraightening (sigmaPresheafVertexFunctor v)) :=
    sigmaPresheafElements_isSifted hC _ (sigmaPresheafVertexFunctor_preservesFiniteProducts v)
  have hsmall := hD (smallRightUnstraightening (sigmaPresheafVertexFunctor v))
    ((SSet.uliftFunctor.{u + 1, u}).map
      (smallRightUnstraighteningProjection (sigmaPresheafVertexFunctor v)) ≫ F₀)
  have hrestrict : HasColimit (sigmaElementsLeftKanComparison v ≫
      leftKanDiagram (sigmaYonedaInfinityMap C) F₀ v) := by
    rw [sigmaElementsLeftKanComparison_diagram]
    exact hsmall
  exact hasColimit_of_equivalentRestriction (sigmaElementsLeftKanComparison v)
    (sigmaElementsLeftKanComparison_isQCatEquivalence v) _ hrestrict

/-- 元の図式と指定単位を保持する、P_Σ Yoneda に沿う全左 Kan 延長が存在する。 -/
lemma sigma_exists_leftKanExtension
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hD : HasSmallSiftedColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ (G : SigmaPresheafInfinity C ⟶ D) (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G)),
      IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β :=
  F1B.exists_kanLeftExtension_of_local_colimits (sigmaYonedaInfinityMap C) F₀
    (sigmaLeftKanDiagram_hasColimit hC hD F₀)

/-- 元の P_Σ Yoneda に沿う左 Kan 延長の、同じ指定単位自身が関手圏で可逆。 -/
lemma sigmaLeftKanExtension_unit_isIso
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    IsIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) :=
  leftKanExtension_unit_isIso_of_fullyFaithful (sigmaYonedaInfinityMap C)
    (sigmaYonedaInfinityMap_isFullyFaithful C) β hβ

/-- 同じ指定単位の逆で、元の C 上の全図式を回収する全関手同型。 -/
def sigmaLeftKanExtensionRecoveryIso
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    FunctorIso (sigmaYonedaInfinityMap C ≫ G) F₀ := by
  have := sigmaLeftKanExtension_unit_isIso β hβ
  exact (asIso (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β))).symm

/-- 小さい sifted 余極限を持つ標的への延長を、元の図式の全同型による回収付きで得る。 -/
lemma sigma_exists_leftKanExtension_with_recovery
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (hD : HasSmallSiftedColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D) :
    ∃ (G : SigmaPresheafInfinity C ⟶ D) (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G)),
      IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β ∧
        Nonempty (FunctorIso (sigmaYonedaInfinityMap C ≫ G) F₀) := by
  obtain ⟨G, β, hβ⟩ := sigma_exists_leftKanExtension hC hD F₀
  exact ⟨G, β, hβ, ⟨sigmaLeftKanExtensionRecoveryIso β hβ⟩⟩

end SerrePositivity.InfinityCategories.HomotopyLimits
