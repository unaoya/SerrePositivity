module

public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.SmallTargetBoundary
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseFaithfulUp
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseExtension
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseDescent

/-!
概要：一般の局所化普遍性の宇宙持ち上げと降下との同値。
方針：大きい境界資料を小さい marked 内ホーン模型へ落とし、延長と充満忠実性を回収する。
規約：源・標的の quasicategory 性や ModelCategory 仮定を追加しない。
使われ方：Ind-S (4)、D-16 向けの一般の IsLocalization の宇宙絶対性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open LocalizationUniverse

/-- 任意の大きい標的で、元の局所化に沿う全前合成は充満忠実。 -/
theorem IsLocalization.precomposition_isFullyFaithful_ulift
    {X D : SSet.{u}} {F : X ⟶ D} {W : Set (X _⦋1⦌)} (hF : IsLocalization F W)
    (E : SSet.{max u v}) [Quasicategory E] :
    IsFullyFaithful ((pre ((SSet.uliftFunctor.{v, u}).map F)).app E) := by
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{v, u}).obj X).obj d) :=
    small_of_injective (f := fun x => x.down) ULift.down_injective
  have (d : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{v, u}).obj D).obj d) :=
    small_of_injective (f := fun x => x.down) ULift.down_injective
  let p := (pre ((SSet.uliftFunctor.{v, u}).map F)).app E
  have hp : IsFullyFaithful (equivalencePathReplacementMap p) :=
    isFullyFaithful_of_positive_boundary _
      (precomposition_path_boundary_of_small_targets ((SSet.uliftFunctor.{v, u}).map F)
        (fun Q _ => precomposition_fullyFaithful_ulift_target hF Q) E)
  have hproj := isQCatEquivalence_of_trivialKanFibration (equivalencePathReplacementProjection p)
  have hsec : IsQCatEquivalence (equivalencePathReplacementSection p) :=
    hproj.cancel_right (by
      rw [equivalencePathReplacementSection_projection]
      exact (QCatEquivalence.refl _).isQCatEquivalence)
  have h := hsec.isFullyFaithful.comp hp
  rw [equivalencePathReplacementSection_map] at h
  exact h

/-- 一般の局所化の同じ射と指定辺集合を任意の大きい宇宙へ持ち上げる。 -/
theorem IsLocalization.ulift {X D : SSet.{u}} {F : X ⟶ D} {W : Set (X _⦋1⦌)}
    (hF : IsLocalization F W) :
    IsLocalization ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W) := by
  apply isLocalization_of_fullyFaithful_extensions _ _ ((invertsEdges_ulift_iff F W).mpr hF.choose)
  · intro E _
    exact hF.precomposition_isFullyFaithful_ulift E
  · intro E _ L hL
    exact hF.exists_extension_ulift L hL

/-- 同じ元の局所化の普遍性は宇宙の持ち上げで保存・反映される。 -/
theorem isLocalization_ulift_iff {X D : SSet.{u}} (F : X ⟶ D) (W : Set (X _⦋1⦌)) :
    IsLocalization ((SSet.uliftFunctor.{v, u}).map F) (ULift.up.{v, u} '' W) ↔
      IsLocalization F W :=
  ⟨IsLocalization.of_ulift, IsLocalization.ulift⟩

end SerrePositivity.InfinityCategories
