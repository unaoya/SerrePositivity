module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRightAdjointFaithful
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveIdempotence

/-!
概要：元の cofiber の実随伴の余単位は可逆である。
方針：零始点矢印への関手同値と全部分圏包含に分解し、全関手圏で充満忠実性を示す。
規約：対象ごとの同型で代用しない。使われ方：差の関手の局所化普遍性への接続。
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
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

local instance cofiberCounitZeroSourceQuasicategory : Quasicategory (zeroSourceArrows X) :=
  fullSubcomplexOnVertices_quasicategory _ _

lemma cofiberRightAdjointZeroSource_isQCatEquivalence :
    IsQCatEquivalence (cofiberRightAdjointZeroSource X) := by
  have h : IsQCatEquivalence (cofiberRightAdjointZeroSource X ≫ zeroSourceArrowTarget X) := by
    rw [cofiberRightAdjointZeroSource_target]
    exact (QCatEquivalence.refl X).isQCatEquivalence
  exact (isQCatEquivalence_of_trivialKanFibration (zeroSourceArrowTarget X)).cancel_right h

/-- 任意のパラメータの全関手圏でも元の右随伴による後合成は充満忠実。 -/
lemma cofiberRightAdjoint_postcomp_fullyFaithful (A : SSet.{u}) :
    IsFullyFaithful ((ihom A).map (cofiberRightAdjoint X)) := by
  have hs := ((cofiberRightAdjointZeroSource_isQCatEquivalence X).postcompose A).isFullyFaithful
  have h := hs.comp (isFullyFaithful_fullSubcomplexFunctorInclusion A
    ((ihom (Δ[1] : SSet.{u})).obj X) IsZeroSourceArrow)
  rw [← CategoryTheory.Functor.map_comp, cofiberRightAdjointZeroSource_inclusion] at h
  exact h

lemma cofiberAdjunction_counitHom_isIso : IsIso (cofiberAdjunction X).counitHom :=
  (cofiberAdjunction X).counitHom_isIso_of_postcompFullyFaithful
    (cofiberRightAdjoint_postcomp_fullyFaithful X X).toHoFullyFaithful

lemma cofiberAdjunction_counit_isIso : IsIso (cofiberAdjunction X).counit := by
  have := cofiberAdjunction_counitHom_isIso X
  exact counit_isIso_of_counitHom _

end SerrePositivity.KST.LocalizingInvariants
