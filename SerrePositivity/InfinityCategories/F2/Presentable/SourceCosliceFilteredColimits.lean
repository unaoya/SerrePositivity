module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SourceCosliceProjectionColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve

/-!
概要：固定始域の coslice は、底の同じ κ-filtered 余極限を持ち、終域射影はそれを保存する。
方針：共終 poset に移り、join の右包含と反復 coslice の全同値で余極限を回収する。
規約：元の圏の全小余完備性や固定始域の compact 性を仮定しない。
使われ方：元の対象への表示の途中段を保つ相対因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：join の右包含が共終なら、coslice の図式の余極限は底の存在から回収できる。
方針：全余錐圏の反復同型と共終制限の同値で始対象を戻す。
規約：全図式と固定始域を保つ。
使われ方：filtered poset 表示の coslice 内での余極限構成。 -/
lemma sourceCoslice_hasColimit_of_rightCofinal
    {K L C : SSet.{u}} [Quasicategory K] [Quasicategory L] [Quasicategory C]
    (p : K ⟶ C) (D : L ⟶ sliceUnder p)
    (hr : IsRightCofinal (joinInr K L)) (hD : HasColimit (D ≫ sliceUnderProjection p)) :
    HasColimit D := by
  have hR : IsQCatEquivalence (Localization.uncurriedSourceRightRestriction D) :=
    (Ind.sliceUnderRestrict_equivalence_of_rightCofinal (joinInr K L) hr
      (sliceUnderUncurry D)).comp (qCatEquivalenceOfIso
        (eqToIso (congrArg sliceUnder (sliceUnderUncurry_projection D)))).isQCatEquivalence
  let e := (qCatEquivalenceOfIso (iteratedSliceUnderIso D)).trans hR.choose
  obtain ⟨c, hc⟩ := hD
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) c, e.symm.map_isInitialVertex hc⟩

/-- 概要：固定始域 coslice は底と同じ κ-filtered 余極限を持つ。
方針：共終な κ-filtered poset の上で底の余極限を作り、元の全余錐圏へ戻す。
規約：始域の compact 性と全小余極限の存在は不要。
使われ方：固定段からの射を含む filtered 表示。 -/
lemma sourceCoslice_hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C]
    (hC : Ind.HasSmallKappaFilteredColimits κ C) (x : C _⦋0⦌) :
    Ind.HasSmallKappaFilteredColimits κ (sliceUnder (SSet.yonedaEquiv.symm x)) := by
  have : Fact κ.IsRegular := ⟨hκ⟩
  intro I hI hIf D
  obtain ⟨J, hJ, f, hfJ, hJN, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) I
  letI := hJ
  have := hfJ
  have := hJN
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hf' : IsRightCofinal f' := Ind.isRightCofinal_ulift f hf
  have : IsFilteredInfinity (nerve J) :=
    isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (nerve J)
  have hweak : IsWeaklyContractible (nerve J) :=
    isWeaklyContractible_of_isFilteredInfinity (nerve J)
  have hr := Localization.sourceJoinInr_ulift_nerve_isRightCofinal.{u, u + 1} J hweak
  have hc : HasColimit (f' ≫ D) := sourceCoslice_hasColimit_of_rightCofinal
    (SSet.yonedaEquiv.symm x) (f' ≫ D) hr
    (hC (nerve J) (f' ≫ D ≫ sliceUnderProjection (SSet.yonedaEquiv.symm x)))
  let e := (Ind.sliceUnderRestrict_equivalence_of_rightCofinal f' hf' D).choose
  obtain ⟨c, hc⟩ := hc
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) c, e.symm.map_isInitialVertex hc⟩

/-- 概要：固定始域 coslice の終域射影は κ-filtered 余極限を保存する。
方針：指定余錐を共終 poset に制限し、同じ全余錐の底の普遍性を戻す。
規約：余錐を選び直さず、元の射影自身の保存性を示す。
使われ方：固定段からの相対表示を元の圏へ射影する。 -/
lemma sourceCoslice_isColimitCone_iff_projection_kappaFiltered {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C] (x : C _⦋0⦌)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder (SSet.yonedaEquiv.symm x))
    (c : JoinCocone D) :
    IsColimitCone c ↔ IsColimitCone
      (mapJoinCocone (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c) := by
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨J, hJ, f, hfJ, hJN, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := κ) I
  letI := hJ
  have := hfJ
  have := hJN
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hf' : IsRightCofinal f' := Ind.isRightCofinal_ulift f hf
  have : IsFilteredInfinity (nerve J) :=
    isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (nerve J)
  have hweak : IsWeaklyContractible (nerve J) :=
    isWeaklyContractible_of_isFilteredInfinity (nerve J)
  have hr := Localization.sourceJoinInr_ulift_nerve_isRightCofinal.{u, u + 1} J hweak
  exact (Ind.isColimitCone_iff_restrict_rightCofinal f' hf' c).trans
    ((Localization.sourceCoslice_isColimitCone_iff_projection
      (SSet.yonedaEquiv.symm x) (f' ≫ D) hr (c.restrict f')).trans
      (Ind.isColimitCone_iff_restrict_rightCofinal f' hf'
        (mapJoinCocone (sliceUnderProjection (SSet.yonedaEquiv.symm x)) c)).symm)

/-- 概要：固定始域 coslice の終域射影は κ-filtered 余極限を保存する。
方針：同じ指定余錐の射影による判定を使う。
規約：元の圏の余極限存在は不要。
使われ方：固定段を保つ表示の元の圏への射影。 -/
lemma sourceCosliceProjection_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C] (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (sliceUnderProjection (SSet.yonedaEquiv.symm x)) := by
  intro I hI hIf D c hc
  exact (sourceCoslice_isColimitCone_iff_projection_kappaFiltered hκ x D c).mp hc

end SerrePositivity.InfinityCategories.F2.Presentable
