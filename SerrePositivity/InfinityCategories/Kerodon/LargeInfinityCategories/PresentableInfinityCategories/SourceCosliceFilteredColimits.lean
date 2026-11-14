module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceProjectionColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.FilteredPosetNerve

/-!
概要：固定始域の coslice は、底の同じ κ-filtered 余極限を持ち、終域射影はそれを保存する。
方針：共終 poset に移り、join の右包含と反復 coslice の全同値で余極限を回収する。
規約：元の圏の全小余完備性や固定始域の compact 性を仮定しない。
使われ方：元の対象への表示の途中段を保つ相対因子化。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：join の右包含が共終なら、coslice の図式の余極限は底の存在から回収できる。
方針：全余錐圏の反復同型と共終制限の同値で始対象を戻す。
規約：全図式と固定始域を保つ。
使われ方：filtered poset 表示の coslice 内での余極限構成。 -/
lemma sourceCoslice_hasColimit_of_rightCofinal
    {K L C : SSet.{u}} [Quasicategory K] [Quasicategory L] [Quasicategory C]
    (p : K ⟶ C) (D : L ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L)) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D := by
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uncurriedSourceRightRestriction D) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L) hr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry D)).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection D)))).isQCatEquivalence
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso D)).trans hR.choose
  obtain ⟨c, hc⟩ := hD
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) c, e.symm.map_isInitialVertex hc⟩

/-- 概要：固定始域 coslice は底と同じ κ-filtered 余極限を持つ。
方針：共終な κ-filtered poset の上で底の余極限を作り、元の全余錐圏へ戻す。
規約：始域の compact 性と全小余極限の存在は不要。
使われ方：固定段からの射を含む filtered 表示。 -/
lemma sourceCoslice_hasSmallKappaFilteredColimits {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x)) := by
  have : Fact κ.IsRegular := ⟨hκ⟩
  intro I hI hIf D
  obtain ⟨J, hJ, f, hfJ, hJN, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := κ) I
  letI := hJ
  have := hfJ
  have := hJN
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (nerve J) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (nerve J)
  have hweak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve J) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity (nerve J)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceJoinInr_ulift_nerve_isRightCofinal.{u, u + 1} J hweak
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (f' ≫ D) := sourceCoslice_hasColimit_of_rightCofinal
    (SSet.yonedaEquiv.symm x) (f' ≫ D) hr
    (hC (nerve J) (f' ≫ D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)))
  let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal f' hf' D).choose
  obtain ⟨c, hc⟩ := hc
  exact ⟨e.inv.app (Opposite.op ⦋0⦌) c, e.symm.map_isInitialVertex hc⟩

/-- 概要：固定始域 coslice の終域射影は κ-filtered 余極限を保存する。
方針：指定余錐を共終 poset に制限し、同じ全余錐の底の普遍性を戻す。
規約：余錐を選び直さず、元の射影自身の保存性を示す。
使われ方：固定段からの相対表示を元の圏へ射影する。 -/
lemma sourceCoslice_isColimitCone_iff_projection_kappaFiltered {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C] (x : C _⦋0⦌)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm x))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c) := by
  have : Fact κ.IsRegular := ⟨hκ⟩
  obtain ⟨J, hJ, f, hfJ, hJN, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := κ) I
  letI := hJ
  have := hfJ
  have := hJN
  let f' := (SSet.uliftFunctor.{u + 1, u}).map f
  have hf' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal f' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsFilteredInfinity (nerve J) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isFilteredInfinity_of_isKappaFiltered hκ.aleph0_le (nerve J)
  have hweak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeaklyContractible (nerve J) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isWeaklyContractible_of_isFilteredInfinity (nerve J)
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceJoinInr_ulift_nerve_isRightCofinal.{u, u + 1} J hweak
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal f' hf' c).trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_isColimitCone_iff_projection
      (SSet.yonedaEquiv.symm x) (f' ≫ D) hr (c.restrict f')).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal f' hf'
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) c)).symm)

/-- 概要：固定始域 coslice の終域射影は κ-filtered 余極限を保存する。
方針：同じ指定余錐の射影による判定を使う。
規約：元の圏の余極限存在は不要。
使われ方：固定段を保つ表示の元の圏への射影。 -/
lemma sourceCosliceProjection_isKappaAccessibleFunctor {κ : Cardinal.{u}}
    (hκ : κ.IsRegular) {C : SSet.{u + 1}} [Quasicategory C] (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) := by
  intro I hI hIf D c hc
  exact (sourceCoslice_isColimitCone_iff_projection_kappaFiltered hκ x D c).mp hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "2.2.2.8" (partial := special) "仮定：準圏の余スライスの図式、join の右包含の共終性（Lean が強い：底 S が一点、図式形状を準圏とする）。結論：指定余錐の余極限性を元の準圏への射影で判定し、底の存在から余スライスの余極限を得る（この場合の (1) と (2) に一致）。底の任意の射に沿う相対版は型に含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasColimit_of_rightCofinal
attribute [cite HTT "5.4.5.14" (partial := special) "仮定：正則 τ と C の小 τ-filtered 余極限の存在（Lean が強い：固定図式を一点 x に限定）。結論：同じ Cx/ は小 τ-filtered 余極限を持つ（この場合に一致）。任意の小形状の p についての存在まではこの宣言で述べていない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCoslice_hasSmallKappaFilteredColimits
