module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaOppositeComma
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafSliceConeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.ConeSectionBaseChange
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteNerveOpposite
public import SerrePositivity.InfinityCategories.F2.Ind.UliftCoconeReverse

/-!
概要：元の P_Σ Yoneda は、有限余積に双対な元の全有限積錐を保存する。
方針：各 P_Σ 前層の保存する全錐を、同じ反転 comma と coslice の切断同値へ移す。
規約：元の全錐と全対象係数を保持し、ホモトピー圏の余積だけへ弱めない。
使われ方：Yoneda の有限余積保存と P_Σ 上の全余極限保存判定。
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

/-- 概要：全 P_Σ 前層が保存する同じ錐は、元の反転 Yoneda でも極限となる。
方針：元の各係数の Yoneda slice の切断同値を、同じ comma と coslice の底変換で戻す。
規約：全係数が保存するという証拠は元の指定錐について要求する。
使われ方：有限余積に双対な全有限積錐の保存。 -/
lemma sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation
    {K C : SSet.{u}} [Quasicategory C] {p : K ⟶ C.op} (c : JoinCone p)
    (h : ∀ w : (SigmaPresheafInfinity C) _⦋0⦌,
      IsLimitCone (mapJoinCone (sigmaPresheafVertexFunctor w) (JoinCone.ulift.{u, u + 1} c))) :
    IsLimitCone (mapJoinCone (oppositeSigmaYoneda C) (JoinCone.ulift.{u, u + 1} c)) := by
  apply (isLimitCone_iff_coneSectionRestriction_homotopyEquivalence _).mpr
  intro x
  let w : (SigmaPresheafInfinity C) _⦋0⦌ := SSet.opObjEquiv x
  let e := SSet.opFunctor.mapIso (sigmaLeftKanCommaIso w).symm
  have he : e.hom ≫ oppositeSigmaLeftKanProjection w =
      oppositeYonedaSliceProjection (sigmaPresheafVertexFunctor w) := by
    change SSet.opFunctor.map (sigmaLeftKanCommaIso w).inv ≫
      (SSet.opFunctor.map (leftKanProjection (sigmaYonedaInfinityMap C) w) ≫
        (uliftOppositeIso C).inv) = _
    rw [← Category.assoc, ← SSet.opFunctor.map_comp, sigmaLeftKanCommaIso_inv_projection]
    rfl
  have hs := presheafYonedaSlice_coneRestriction_of_isLimit (sigmaPresheafVertexFunctor w) c (h w)
  have hm := (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (oppositeYonedaSliceProjection (sigmaPresheafVertexFunctor w))
    (oppositeSigmaLeftKanProjection w) e.hom he (isPrecompositionEquivalence_of_iso e)
    (JoinCone.ulift.{u, u + 1} c)).mp hs
  let q := sliceUnderProjection (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm w))
  let y := oppositeSigmaYoneda C
  have : LeftFibration (CategoryTheory.Limits.pullback.snd q y) :=
    ⟨leftFibrations.pullback_snd q y (LeftFibration.mem (p := q))⟩
  have hb := (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (oppositeSigmaLeftKanProjection w) (CategoryTheory.Limits.pullback.snd q y)
    (sigmaCommaCoslicePullbackIso w).hom (sigmaCommaCoslicePullbackIso_projection w)
    (isPrecompositionEquivalence_of_iso (sigmaCommaCoslicePullbackIso w))
    (JoinCone.ulift.{u, u + 1} c)).mp hm
  have ht := (leftFibrationConeRestriction_baseChange_iff q y
    (JoinCone.ulift.{u, u + 1} c)).mp hb
  change IsQCatEquivalence (coneSectionRestriction
    (mapJoinCone y (JoinCone.ulift.{u, u + 1} c)) (SSet.opObjEquiv.symm w)) at ht
  have hx : SSet.opObjEquiv.symm w = x := Equiv.symm_apply_apply _ x
  rw [hx] at ht
  exact ht.isSimplicialHomotopyEquivalence

/-- 概要：元の P_Σ Yoneda の反転は、元の全有限積錐を保存する。
方針：P_Σ の全前層の有限積保存を、全係数の切断による判定へ渡す。
規約：空の有限添字も含み、元の指定全錐を保持する。
使われ方：P_Σ Yoneda の元の有限余積保存の双対的な公開界面。 -/
lemma sigmaYoneda_finiteOppositeCone_isLimit {C : SSet.{u}} [Quasicategory C]
    {J : Type u} [Finite J] {p : nerve (CategoryTheory.Discrete J) ⟶ C.op}
    (c : JoinCone p) (hc : IsLimitCone c) :
    IsLimitCone (mapJoinCone (oppositeSigmaYoneda C) (JoinCone.ulift.{u, u + 1} c)) :=
  sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation c
    (fun w ↦ sigmaPresheafVertexFunctor_preservesFiniteProducts w J p c hc)

/-- 概要：元の P_Σ Yoneda は元の有限余積の指定全余錐を保存する。
方針：全係数の有限積保存を反転全錐に適用し、宇宙比較で元の余錐へ戻す。
規約：空添字を含み、元の頂点と全脚を保持する。
使われ方：P_Σ の有限余積と全余極限保存判定。 -/
lemma sigmaYoneda_finiteCoproduct_isColimit {C : SSet.{u}} [Quasicategory C]
    {J : Type u} [Finite J] {p : nerve (Discrete J) ⟶ C}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone (sigmaYonedaInfinityMap C)
      (JoinCocone.ulift.{u, u + 1} c)) := by
  have hr : IsLimitCone (F1B.coconeReverseCone c) :=
    (F1B.isColimitCone_iff_reverseCone c).mp hc
  have hσ := sigmaYoneda_oppositeCone_isLimit_of_vertexPreservation
    (F1B.coconeReverseCone c) (fun w ↦
      (sigmaPresheafVertexFunctor_preservesFiniteProducts w).map_isLimit_of_shapeIso
        (discreteNerveOppositeIso J).symm _ hr)
  let t := mapJoinCone (SSet.opFunctor.map (sigmaYonedaInfinityMap C))
    (F1B.coconeReverseCone (JoinCocone.ulift.{u, u + 1} c))
  have hv : (mapJoinCone (oppositeSigmaYoneda C)
      (JoinCone.ulift.{u, u + 1} (F1B.coconeReverseCone c))).val =
      (restrictJoinCone t (uliftOppositeIso (nerve (Discrete J))).hom).val := by
    change _ ≫ (uliftOppositeIso C).hom ≫
      SSet.opFunctor.map (sigmaYonedaInfinityMap C) = _
    rw [← Category.assoc]
    erw [uliftCoconeReverse_val c]
    exact Category.assoc _ _ _
  apply (F2.isLimitCone_reverse_postcomp_iff _ _).mp
  apply (F2.isLimitCone_restrict_iff_of_isIso t
    (uliftOppositeIso (nerve (Discrete J))).hom).mp
  exact (F2.isLimitCone_iff_of_cone_val_eq _ _ hv).mp hσ

end SerrePositivity.InfinityCategories.HomotopyLimits
