module

public import SerrePositivity.InfinityCategories.F2.Ind.IndCommaPullbackIso
public import SerrePositivity.InfinityCategories.F2.Ind.ConeSectionBaseChange

/-!
概要：元の指定有限余極限の反転全錐を、元の Ind Yoneda の反転が極限全錐へ送る。
方針：実際の Ind comma の切断制限を厳密な底変換へ移し、全係数で極限性を検出する。
規約：交換入力を明示。元の全錐・元の Yoneda と全対象係数を保つ。
使われ方：宇宙と反転の順序の正規化を経た native な有限余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
  {K C : SSet.{u}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
  (c : JoinCocone D) (hc : IsColimitCone c)
include hκ hex hc

/-- 元の任意の Ind 対象の coslice 上で、同じ全錐の像の切断制限自身が同値。 -/
lemma ind_finiteColimit_cosliceSections_isQCatEquivalence (w : (IndInfinity κ C) _⦋0⦌) :
    IsQCatEquivalence (leftFibrationConeRestriction
      (sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w)))
      (mapJoinCone (oppositeIndYoneda κ)
        (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)))) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w))
  let y := oppositeIndYoneda (C := C) κ
  letI : LeftFibration (pullback.snd p y) :=
    ⟨leftFibrations.pullback_snd p y (LeftFibration.mem (p := p))⟩
  have hb := (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (oppositeIndLeftKanProjection κ w) (pullback.snd p y)
    (indCommaCoslicePullbackIso κ w).hom (indCommaCoslicePullbackIso_projection κ w)
    (isPrecompositionEquivalence_of_iso (indCommaCoslicePullbackIso κ w))
    (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))).mp
      (ind_finiteColimit_commaSections_isQCatEquivalence κ hκ hex c hc w)
  exact (leftFibrationConeRestriction_baseChange_iff p y _).mp hb

/-- 明示交換入力のもとで、同じ元の有限余極限の反転全錐の Yoneda 像は極限。 -/
lemma indYoneda_finiteOppositeCone_isLimit :
    IsLimitCone (mapJoinCone (oppositeIndYoneda κ)
      (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))) := by
  apply (isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mpr
  intro x
  have h := ind_finiteColimit_cosliceSections_isQCatEquivalence κ hκ hex c hc (SSet.opObjEquiv x)
  have hx : SSet.opObjEquiv.symm (SSet.opObjEquiv x) = x := Equiv.symm_apply_apply _ x
  rw [hx] at h
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.F2.Ind
