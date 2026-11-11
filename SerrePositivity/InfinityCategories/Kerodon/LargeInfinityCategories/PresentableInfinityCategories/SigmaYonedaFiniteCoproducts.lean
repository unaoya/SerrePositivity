module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaOppositeComma
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PresheafSliceConeRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeSectionBaseChange
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiscreteNerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.UliftCoconeReverse

/-!
概要：元の P_Σ Yoneda は、有限余積に双対な元の全有限積錐を保存する。
方針：各 P_Σ 前層の保存する全錐を、同じ反転 comma と coslice の切断同値へ移す。
規約：元の全錐と全対象係数を保持し、ホモトピー圏の余積だけへ弱めない。
使われ方：Yoneda の有限余積保存と P_Σ 上の全余極限保存判定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：全 P_Σ 前層が保存する同じ錐は、元の反転 Yoneda でも極限となる。
方針：元の各係数の Yoneda slice の切断同値を、同じ comma と coslice の底変換で戻す。
規約：全係数が保存するという証拠は元の指定錐について要求する。
使われ方：有限余積に双対な全有限積錐の保存。 -/
lemma sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation
    {K C : SSet.{u}} [Quasicategory C] {p : K ⟶ C.op} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p)
    (h : ∀ w : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor w) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaYoneda C) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mpr
  intro x
  let w : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C) _⦋0⦌ := SSet.opObjEquiv x
  let e := SSet.opFunctor.mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanCommaIso w).symm
  have he : e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaLeftKanProjection w =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.oppositeYonedaSliceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor w) := by
    change SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanCommaIso w).inv ≫
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) w) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).inv) = _
    rw [← Category.assoc, ← SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaLeftKanCommaIso_inv_projection]
    rfl
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.presheafYonedaSlice_coneRestriction_of_isLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor w) c (h w)
  have hm := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.oppositeYonedaSliceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor w))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaLeftKanProjection w) e.hom he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e)
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)).mp hs
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w))
  let y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaYoneda C
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (CategoryTheory.Limits.pullback.snd q y) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd q y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := q))⟩
  have hb := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaLeftKanProjection w) (CategoryTheory.Limits.pullback.snd q y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaCommaCoslicePullbackIso w).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaCommaCoslicePullbackIso_projection w)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaCommaCoslicePullbackIso w))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)).mp hm
  have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFibrationConeRestriction_baseChange_iff q y
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)).mp hb
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneSectionRestriction
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone y (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) (SSet.opObjEquiv.symm w)) at ht
  have hx : SSet.opObjEquiv.symm w = x := Equiv.symm_apply_apply _ x
  rw [hx] at ht
  exact ht.isSimplicialHomotopyEquivalence

/-- 概要：元の P_Σ Yoneda の反転は、元の全有限積錐を保存する。
方針：P_Σ の全前層の有限積保存を、全係数の切断による判定へ渡す。
規約：空の有限添字も含み、元の指定全錐を保持する。
使われ方：P_Σ Yoneda の元の有限余積保存の双対的な公開界面。 -/
lemma sigmaYoneda_finiteOppositeCone_isLimit {C : SSet.{u}} [Quasicategory C]
    {J : Type u} [Finite J] {p : nerve (CategoryTheory.Discrete J) ⟶ C.op}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaYoneda C) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) :=
  sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation c
    (fun w ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_preservesFiniteProducts w J p c hc)

/-- 概要：元の P_Σ Yoneda は元の有限余積の指定全余錐を保存する。
方針：全係数の有限積保存を反転全錐に適用し、宇宙比較で元の余錐へ戻す。
規約：空添字を含み、元の頂点と全脚を保持する。
使われ方：P_Σ の有限余積と全余極限保存判定。 -/
lemma sigmaYoneda_finiteCoproduct_isColimit {C : SSet.{u}} [Quasicategory C]
    {J : Type u} [Finite J] {p : nerve (Discrete J) ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} c)) := by
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_reverseCone c).mp hc
  have hσ := sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c) (fun w ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexFunctor_preservesFiniteProducts w).map_isLimit_of_shapeIso
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.discreteNerveOppositeIso J).symm _ hr)
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u, u + 1} c))
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.oppositeSigmaYoneda C)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone c))).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve (Discrete J))).hom).val := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso C).hom ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaYonedaInfinityMap C) = _
    rw [← Category.assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.uliftCoconeReverse_val c]
    exact Category.assoc _ _ _
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_reverse_postcomp_iff _ _).mp
  apply (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.uliftOppositeIso (nerve (Discrete J))).hom).mp
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv).mp hσ

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
