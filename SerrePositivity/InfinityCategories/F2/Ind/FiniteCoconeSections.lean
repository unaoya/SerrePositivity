module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitExactness
public import SerrePositivity.InfinityCategories.F1.NativePointedRestrictionReflection
public import SerrePositivity.InfinityCategories.F1.CoherentPointedRestrictionReflection

/-!
概要：有限余極限の同じ全余錐に対する Ind 前層の保存性を、実際の小さい切断制限へ戻す。
方針：元の反転錐の pointed 制限の同値性を、小さい全空間の切断へ反映する。
規約：交換入力を明示し、元の図式・全余錐・境界射を固定する。
使われ方：元の Yoneda slice 比較を通した Ind 内の有限余極限の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 元の全余錐の反転錐の、元の図式を固定する右境界包含。 -/
def oppositeCoconeBoundary {K C : SSet.{u}} {D : K ⟶ C} (c : JoinCocone D) :
    Over.mk (SSet.opFunctor.map D) ⟶ Over.mk (F1B.kanCoconeReverseCone c).val :=
  Over.homMk (joinInr (Δ[0] : SSet.{u}) K.op) (F1B.kanCoconeReverseCone c).property

/-- 明示交換入力のもとで、同じ元の反転余錐から底への小さい切断制限自身が同値。 -/
lemma indPresheaf_finiteColimit_smallSectionRestriction_isQCatEquivalence
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {K C : SSet.{u}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsIndVertex κ C (functorVertex F)) :
    IsQCatEquivalence (relativeFunctorOverPre (smallLeftUnstraighteningProjection F)
      (oppositeCoconeBoundary c)) := by
  have ht := indPresheaf_finiteColimit_isLimit κ hκ hex c hc F hF
  have hs := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mp ht
    pointSpaceVertex).isQCatEquivalence
  have hp := coherentPointedRestriction_of_nativeCone_isQCatEquivalence
    (F1B.kanCoconeReverseCone c) F hs
  exact relativeRestriction_isQCatEquivalence_of_coherentPointed F (oppositeCoconeBoundary c) hp

end SerrePositivity.InfinityCategories.F2.Ind
