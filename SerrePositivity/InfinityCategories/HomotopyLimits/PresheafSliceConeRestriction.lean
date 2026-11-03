module

public import SerrePositivity.InfinityCategories.HomotopyLimits.Ind.YonedaSliceOppositeComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.Ind.LiftedConeSectionRestriction
public import SerrePositivity.InfinityCategories.F1.Transport.NativePointedRestrictionReflection
public import SerrePositivity.InfinityCategories.F1.Coherent.PointedRestrictionReflection

/-!
概要：前層が保存する元の全錐について、同じ Yoneda slice 上の切断制限は同値である。
方針：元の一点切断判定を小さい復元へ戻し、反転・宇宙変更・Yoneda 比較で移送する。
規約：濃度や Ind 条件は要求せず、同じ指定錐像の極限性を使う。
使われ方：P_Σ Yoneda の有限余積保存の全係数判定。
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

/-- 概要：元の前層が保存する全錐の、小さい left fibration 上の切断制限は同値である。
方針：元の錐像の一点切断制限を、同じ小さい復元の相対制限へ反映する。
規約：錐や始域の有限性は要求しない。
使われ方：同じ錐の Yoneda slice への移送の始点。 -/
lemma smallLeftUnstraightening_coneRestriction_of_isLimit {K C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    {p : K ⟶ C.op} (c : JoinCone p)
    (hc : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c))) :
    IsQCatEquivalence (leftFibrationConeRestriction (smallLeftUnstraighteningProjection F) c) := by
  let g : Over.mk p ⟶ Over.mk c.val := Over.homMk (joinInr (Δ[0] : SSet.{u}) K) c.property
  have hs := ((isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mp hc
    pointSpaceVertex).isQCatEquivalence
  have hp := coherentPointedRestriction_of_nativeCone_isQCatEquivalence c F hs
  rw [leftFibrationConeRestriction_eq_overPre]
  exact relativeRestriction_isQCatEquivalence_of_coherentPointed F g hp

/-- 概要：元の錐像が極限なら、同じ反転 Yoneda slice 上の全切断制限は同値である。
方針：小さい復元からの制限を反転同型・宇宙持ち上げ・既存の Yoneda 比較で移す。
規約：元の全錐の同じ持ち上げを使い、別の錐へ置換しない。
使われ方：P_Σ の各対象係数における有限余積の普遍性。 -/
lemma presheafYonedaSlice_coneRestriction_of_isLimit {K C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    {p : K ⟶ C.op} (c : JoinCone p)
    (hc : IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c))) :
    IsQCatEquivalence (leftFibrationConeRestriction (oppositeYonedaSliceProjection F)
      (JoinCone.ulift.{u, u + 1} c)) := by
  have hs := smallLeftUnstraightening_coneRestriction_of_isLimit F c hc
  have hr := (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (SSet.opFunctor.map (smallRightUnstraighteningProjection F))
    (smallLeftUnstraighteningProjection F) (smallRightUnstraighteningOppositeIso F).hom
    (smallRightUnstraighteningProjection_op F).symm
    (isPrecompositionEquivalence_of_iso (smallRightUnstraighteningOppositeIso F)) c).mpr hs
  have hu := leftFibrationConeRestriction_isQCatEquivalence_ulift _ _ hr
  exact (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    ((SSet.uliftFunctor.{u + 1, u}).map
      (SSet.opFunctor.map (smallRightUnstraighteningProjection F)))
    (oppositeYonedaSliceProjection F) (oppositeElementsYonedaSliceComparison F)
    (oppositeElementsYonedaSliceComparison_projection F)
    (oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence F)
    (JoinCone.ulift.{u, u + 1} c)).mp hu

end SerrePositivity.InfinityCategories.HomotopyLimits
