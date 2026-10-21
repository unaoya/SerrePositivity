module

public import SerrePositivity.KST.LocalizingInvariants.WalkingEquivalenceRestriction

/-!
概要：自由な可逆区間の図式の制限は、可逆辺の関手圏への trivial Kan fibration。
方針：二つのパラメータを交換し、core 上の anodyne 相対充填を元の制限の充填へ戻す。
規約：非定値図式の全関手 ∞ 圏の普遍性。使われ方：一般商の辺反転を貼り合わせる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma walkingEquivalenceRestriction_lifting {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] : HasLiftingProperty i (walkingEquivalenceRestriction X) := by
  constructor
  intro u v sq
  let U := internalHomFlipHomEquiv A walkingEquivalence X u
  let V := internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X (v ≫ equivalencePathι X)
  have h : V ≫ (pre i).app X = walkingEquivalenceEdge ≫ U := by
    have hs := congrArg (fun f => f ≫ equivalencePathι X) sq.w
    rw [Category.assoc, walkingEquivalenceRestriction_ι, Category.assoc] at hs
    have ht := congrArg (internalHomFlipHomEquiv A (Δ[1] : SSet.{u}) X) hs
    rw [internalHomFlipHomEquiv_pre_app, internalHomFlipHomEquiv_pre] at ht
    exact ht.symm
  obtain ⟨l, hl, hr⟩ := walkingEquivalence_relative_extension ((pre i).app X)
    (F1B.kanEquivalenceLifting_pre i) V (equivalencePath_flip_invertible v) U h
  let r := (internalHomFlipHomEquiv B walkingEquivalence X).symm l
  refine CommSq.HasLift.mk' { l := r, fac_left := ?_, fac_right := ?_ }
  · apply (internalHomFlipHomEquiv A walkingEquivalence X).injective
    rw [internalHomFlipHomEquiv_pre]
    change (internalHomFlipHomEquiv B walkingEquivalence X)
      ((internalHomFlipHomEquiv B walkingEquivalence X).symm l) ≫ (pre i).app X = U
    rw [Equiv.apply_symm_apply, hr]
  · have : Mono (equivalencePathι X) :=
      inferInstanceAs (Mono (fullSubcomplexOnVertices _ IsEquivalencePathVertex).ι)
    apply (cancel_mono (equivalencePathι X)).mp
    rw [Category.assoc, walkingEquivalenceRestriction_ι]
    apply (internalHomFlipHomEquiv B (Δ[1] : SSet.{u}) X).injective
    rw [internalHomFlipHomEquiv_pre_app]
    change walkingEquivalenceEdge ≫ (internalHomFlipHomEquiv B walkingEquivalence X)
      ((internalHomFlipHomEquiv B walkingEquivalence X).symm l) = V
    rw [Equiv.apply_symm_apply, hl]

instance walkingEquivalenceRestriction_trivialKanFibration (X : SSet.{u}) [Quasicategory X] :
    TrivialKanFibration (walkingEquivalenceRestriction X) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  exact walkingEquivalenceRestriction_lifting (boundary n).ι

lemma walkingEquivalenceRestriction_isQCatEquivalence (X : SSet.{u}) [Quasicategory X] :
    IsQCatEquivalence (walkingEquivalenceRestriction X) :=
  isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.KST.LocalizingInvariants
