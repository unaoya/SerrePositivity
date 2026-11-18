module

public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsLeftLimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LocalShapeOppositeHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointSliceReverseCoordinates
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCosliceEdge
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityIntervalAtLeg
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafRightFiberPointedIso

/-!
概要：右 Kan 添字の同じ頂点から読んだ辺は、元の密度余錐の脚の反転である。
方針：引き戻しの第1射影と点 slice の反転を計算し、元の余錐の同じ実脚を読む。
使われ方：離散前層の密度の脚の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

namespace SerrePositivity.InfinityCategories.Sheaves

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

private theorem leftElementsRightKanComparison_coslice :
    let U := SSet.uliftFunctor.{u + 1, u}
    let y := yonedaInfinityMap C
    let z := functorVertex F
    let b := SSet.opObjEquiv.symm z
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm b)
    leftElementsRightKanComparison F ≫ pullback.fst q (SSet.opFunctor.map y) =
      U.map (smallRightUnstraighteningOppositeIso F).inv ≫
        (uliftOppositeIso (smallRightUnstraightening F)).hom ≫
        SSet.opFunctor.map (presheafDensitySliceMap F) ≫
          (cofinalPointSliceOverOpIso z).hom.left := by
  intro U y z b q
  dsimp only [U, q, b, y, z]
  simp only [leftElementsRightKanComparison, presheafElementsRightKanComparison,
    Category.assoc]
  erw [kanLeftKanShapeOpIso_slice (yonedaInfinityMap C) (functorVertex F)]
  simp only [← Category.assoc,
    ← Functor.map_comp, presheafElementsLeftKanComparison]
  simp only [Category.assoc]
  erw [pullbackSymmetry_inv_comp_snd (f := yonedaInfinityMap C)
    (g := sliceOverProjection (SSet.yonedaEquiv.symm (functorVertex F)))]
  erw [presheafElementsYonedaSliceComparison, pullback.lift_fst]



private theorem cofinalPointSliceOverOpIso_edge
    {X : SSet.{u}} (z : X _⦋0⦌) (s : (sliceOver (SSet.yonedaEquiv.symm z)) _⦋0⦌) :
    let u := ((cofinalPointSliceOverOpIso z).hom.left).app (Opposite.op ⦋0⦌)
      (SSet.opObjEquiv.symm s)
    (pointCosliceVertexEdge (SSet.yonedaEquiv.symm (SSet.opObjEquiv.symm z)) u).edge =
      SSet.opObjEquiv.symm (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ s.val)) := by
  intro v
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ v.val) = _
  dsimp only [v]
  rw [cofinalPointSliceOverOpIso_app_val, Equiv.apply_symm_apply]
  have hRev := pointJoinReverseIso_inv_coordinates.{u} 0
  have hIso : leftPointStdSimplexIso.{u} 0 = joinStdSimplexIso 0 0 :=
    stdSimplexIso_unique 1 _ _
  have hS :
      s.val = (joinStdSimplexIso 0 0).hom ≫ ((joinStdSimplexIso 0 0).inv ≫ s.val) :=
    (Iso.hom_inv_id_assoc (joinStdSimplexIso 0 0) s.val).symm
  conv_lhs =>
    rw [hS, Functor.map_comp]
  have hComp := congrArg (fun k => (joinStdSimplexIso 0 0).inv ≫ k ≫
    SSet.opFunctor.map ((joinStdSimplexIso 0 0).inv ≫ s.val)) hRev
  simp only [Category.assoc, hIso, Iso.inv_hom_id_assoc] at hComp
  simp only [Category.assoc]
  exact (congrArg SSet.yonedaEquiv hComp).trans (stableReverseSimplex_yoneda _ _)


variable (x : C _⦋0⦌)

/-- 右 Kan 添字の同じ頂点から読んだ辺は、元の密度余錐の脚の反転である。
Kerodon §9.3（Tag 06FR）の密度比較。HTT 5.1.5.6 に使う脚の一次座標の照合。 -/
lemma leftElementsRightKanComparison_point_edge
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    let R := presheafRightFiberLeftIso F x
    let v := R.hom.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm s)
    let z := functorVertex F
    let b := SSet.opObjEquiv.symm z
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm b)
    let r := SSet.opFunctor.map (yonedaInfinityMap C)
    let w := (leftElementsRightKanComparison F ≫ pullback.fst q r).app
      (Opposite.op ⦋0⦌) (ULift.up v.val)
    (pointCosliceVertexEdge (SSet.yonedaEquiv.symm b) w).edge =
      SSet.opObjEquiv.symm
        (coconeVertexLeg (presheafDensityCocone F) (ULift.up s.val)).edge := by
  intro R v z b q r w
  let U := SSet.uliftFunctor.{u + 1, u}
  let E := smallRightUnstraightening F
  let M := smallRightUnstraighteningOppositeIso F
  let e₀ := (SSet.opObjEquiv (X := E)).symm s.val
  have hs₀ : M.hom.app (Opposite.op ⦋0⦌) e₀ = v.val := by
    have hh := presheafRightFiberLeftIso_ι F x
    have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm s)) hh
    exact h.symm
  have hs₁ : M.inv.app (Opposite.op ⦋0⦌) v.val = e₀ := by
    rw [← hs₀]
    exact congrArg (fun k : E.op ⟶ E.op => k.app (Opposite.op ⦋0⦌) e₀) M.hom_inv_id
  let t := presheafDensitySliceMap F
  let s₀ : (U.obj E) _⦋0⦌ := ULift.up s.val
  let c₀ := (cofinalPointSliceOverOpIso z).hom.left
  have hw : w = c₀.app (Opposite.op ⦋0⦌) (SSet.opObjEquiv.symm
      (t.app (Opposite.op ⦋0⦌) s₀)) := by
    have hh := leftElementsRightKanComparison_coslice F
    have h := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (ULift.up v.val)) hh
    change w = (U.map M.inv ≫ (uliftOppositeIso E).hom ≫ SSet.opFunctor.map t ≫ c₀).app
      (Opposite.op ⦋0⦌) (ULift.up v.val) at h
    rw [h]
    have hU : ((U.map M.inv).app (Opposite.op ⦋0⦌)) (ULift.up v.val) = ULift.up e₀ :=
      congrArg ULift.up hs₁
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, hU]
    rfl
  rw [hw]
  rw [cofinalPointSliceOverOpIso_edge]
  have ht : (t.app (Opposite.op ⦋0⦌) s₀).val =
      joinMap (SSet.yonedaEquiv.symm s₀) (𝟙 Δ[0]) ≫ (presheafDensityCocone F).val := by
    have hh : sliceOverUncurry t = (presheafDensityCocone F).val := by
      dsimp only [t, presheafDensitySliceMap]
      rw [sliceOverUncurry_curry]
    have he := congrArg (fun k => joinMap (SSet.yonedaEquiv.symm s₀) (𝟙 Δ[0]) ≫ k) hh
    rw [← sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda] at he
    exact he
  rw [ht]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
