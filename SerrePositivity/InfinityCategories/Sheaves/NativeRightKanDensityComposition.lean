module

public import SerrePositivity.InfinityCategories.Sheaves.RightKanIntervalCosliceComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityLegPointedComposition
public import SerrePositivity.InfinityCategories.Sheaves.NativeDiscretePresheafEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Sheaves.NativeRightKanDensityLeg

/-!
概要：元の離散変換に沿う密度脚の合成を反対圏へ移し、指定した右 Kan の二つの添字の脚に同定する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open CategoryTheory Limits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 固定図式に移した辺の反転は、元の辺を反転してから固定図式へ移した一単体。 -/
lemma nativeDiscreteEdge_opSimplex
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    (edgeOp (nativeDiscreteEdge φ).toTruncated).edge =
      ((edgeOp (((nerve.edgeMk φ).map (discretePresheafInclusion C).val).toTruncated)).map
        ((truncation 2).map ((SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv))).edge := rfl

private lemma nativeDensityLeg_op_comp
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (x : (nerve C) _⦋0⦌) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let i := nerveOppositeIso (C := C)
    let F := U.map i.hom ≫ discretePresheaf P
    let G := U.map i.hom ≫ discretePresheaf Q
    let L := smallLeftUnstraighteningBaseIso i (discretePresheaf P)
    let R := smallLeftUnstraighteningBaseIso i (discretePresheaf Q)
    let m := L.hom ≫ smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫ R.inv
    let b := SSet.opObjEquiv.symm x
    ∀ (hm : m ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F)
      (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌)
      (t : (vertexFiber (smallRightUnstraighteningProjection G) x) _⦋0⦌),
    let p := (presheafRightFiberLeftIso F x).hom.app _ (SSet.opObjEquiv.symm s)
    let q := (presheafRightFiberLeftIso G x).hom.app _ (SSet.opObjEquiv.symm t)
    (vertexFiberMap (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G)
      m hm b).app _ p = q →
    Truncated.HomotopyCategory.homMk (edgeOp (nativeDiscreteEdge φ).toTruncated) ≫
        Truncated.HomotopyCategory.homMk (edgeOp (densityLegAt F x s).toTruncated) =
      Truncated.HomotopyCategory.homMk (edgeOp (densityLegAt G x t).toTruncated) := by
  intro U i F G L R m b hm s t p q hp
  have H := densityLegAt_baseAction_comp i (discretePresheafHom φ) x hm s t
    (nativeDiscreteEdge φ) hp (nativeDiscreteEdge_evaluation_hom φ b)
  obtain ⟨h⟩ := compStruct_nonempty_of_homMk_fac H
  exact Truncated.HomotopyCategory.homMk_comp_homMk (compStructOp h)

private noncomputable def rightFiberOfLeftPoint
    {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u+1,u}).obj C.op ⟶ SpaceInfinity.{u})
    (x : C _⦋0⦌)
    (s : (vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x)) _⦋0⦌) :
    (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌ :=
  SSet.opObjEquiv ((presheafRightFiberLeftIso F x).inv.app _ s)

private lemma rightFiberOfLeftPoint_roundtrip
    {C : SSet.{u}}
    (F : (SSet.uliftFunctor.{u+1,u}).obj C.op ⟶ SpaceInfinity.{u})
    (x : C _⦋0⦌)
    (s : (vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x)) _⦋0⦌) :
    (presheafRightFiberLeftIso F x).hom.app _ (SSet.opObjEquiv.symm (rightFiberOfLeftPoint F x s)) =
      s := by
  rw [rightFiberOfLeftPoint, Equiv.symm_apply_apply]
  let R := presheafRightFiberLeftIso F x
  let B := vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x)
  have hr : R.inv ≫ R.hom = 𝟙 B := R.inv_hom_id
  exact congrArg (fun f : B ⟶ B => f.app (Opposite.op ⦋0⦌) s) hr

private lemma discreteBaseAction_projection
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let i := nerveOppositeIso (C := C)
    let F := U.map i.hom ≫ discretePresheaf P
    let G := U.map i.hom ≫ discretePresheaf Q
    let L := smallLeftUnstraighteningBaseIso i (discretePresheaf P)
    let R := smallLeftUnstraighteningBaseIso i (discretePresheaf Q)
    let m := L.hom ≫ smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫ R.inv
    m ≫ smallLeftUnstraighteningProjection G = smallLeftUnstraighteningProjection F := by
  intro U i F G L R m
  have hR : R.inv ≫ smallLeftUnstraighteningProjection G =
      smallLeftUnstraighteningProjection (discretePresheaf Q) ≫ i.inv := by
    apply (cancel_epi R.hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, smallLeftUnstraighteningBaseIso_projection,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [m, Category.assoc]
  rw [hR, ← Category.assoc (smallUnstraighteningFunctorHom (discretePresheafHom φ)),
    smallUnstraighteningFunctorHom_projection, ← Category.assoc L.hom,
    smallLeftUnstraighteningBaseIso_projection, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma homMk_comp_transfer_of_simplex_eq
    {X : SSet.{u}} {a b c c' : X _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj X) a b)
    (s : Truncated.Edge (X := (truncation 2).obj X) b c)
    (t : Truncated.Edge (X := (truncation 2).obj X) a c)
    (s' : Truncated.Edge (X := (truncation 2).obj X) b c')
    (t' : Truncated.Edge (X := (truncation 2).obj X) a c')
    (hs : s.edge = s'.edge) (ht : t.edge = t'.edge)
    (h : Truncated.HomotopyCategory.homMk e ≫ Truncated.HomotopyCategory.homMk s =
        Truncated.HomotopyCategory.homMk t) :
    Truncated.HomotopyCategory.homMk e ≫ Truncated.HomotopyCategory.homMk s' =
      Truncated.HomotopyCategory.homMk t' := by
  have hc : c = c' := s.tgt_eq.symm.trans
    ((congrArg (X.δ 0) hs).trans s'.tgt_eq)
  subst c'
  have hss : s = s' := Truncated.Edge.ext hs
  have htt : t = t' := Truncated.Edge.ext ht
  simpa only [← hss, ← htt] using h

private lemma leftElementsRightKanComparison_leftPoint_edge
    {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u+1,u}).obj C.op ⟶ SpaceInfinity.{u})
    (x : C _⦋0⦌)
    (p : (vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x)) _⦋0⦌) :
    let v := SSet.opObjEquiv.symm (functorVertex F)
    let q := sliceUnderProjection (SSet.yonedaEquiv.symm v)
    let δ := SSet.opFunctor.map (yonedaInfinityMap C)
    ∀ (y : (PresheafInfinity C).op _⦋0⦌) (f : (vertexFiber q y) _⦋0⦌),
    f.val = (leftElementsRightKanComparison F ≫ pullback.fst q δ).app
      (Opposite.op ⦋0⦌) (ULift.up p.val) →
    (edgeOp (densityLegAt F x (rightFiberOfLeftPoint F x p)).toTruncated).edge =
      (normalizedCosliceFiberEdge v y f).edge := by
  intro v q δ y f hf
  let s := rightFiberOfLeftPoint F x p
  have hh := leftElementsRightKanComparison_point_edge F x s
  dsimp only at hh
  rw [rightFiberOfLeftPoint_roundtrip F x p] at hh
  change _ = (pointCosliceVertexEdge (SSet.yonedaEquiv.symm v) f.val).edge
  rw [hf]
  exact hh.symm

lemma discreteRightKan_projectedLegs_comp
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let i := nerveOppositeIso (C := C)
    let F := U.map i.hom ≫ discretePresheaf P
    let G := U.map i.hom ≫ discretePresheaf Q
    let L := smallLeftUnstraighteningBaseIso i (discretePresheaf P)
    let R := smallLeftUnstraighteningBaseIso i (discretePresheaf Q)
    let m := L.hom ≫ smallUnstraighteningFunctorHom (discretePresheafHom φ) ≫ R.inv
    let j₀ := U.map m ≫ leftElementsRightKanComparison G
    let j₁ := leftElementsRightKanComparison F
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    let v₀ := SSet.opObjEquiv.symm (functorVertex G)
    let v₁ := SSet.opObjEquiv.symm (functorVertex F)
    let q₀ := sliceUnderProjection (SSet.yonedaEquiv.symm v₀)
    let q₁ := sliceUnderProjection (SSet.yonedaEquiv.symm v₁)
    ∀ (d : (U.obj (smallLeftUnstraightening F)) _⦋0⦌)
      (v : (PresheafInfinity (nerve C)).op _⦋0⦌)
      (f₀ : (vertexFiber q₀ v) _⦋0⦌) (f₁ : (vertexFiber q₁ v) _⦋0⦌),
    f₀.val = (j₀ ≫ pullback.fst q₀ δ).app (Opposite.op ⦋0⦌) d →
    f₁.val = (j₁ ≫ pullback.fst q₁ δ).app (Opposite.op ⦋0⦌) d →
    Truncated.HomotopyCategory.homMk (edgeOp (nativeDiscreteEdge φ).toTruncated) ≫
        Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge v₁ v f₁) =
      Truncated.HomotopyCategory.homMk (normalizedCosliceFiberEdge v₀ v f₀) := by
  intro U i F G L R m j₀ j₁ δ v₀ v₁ q₀ q₁ d v f₀ f₁ h₀ h₁
  let b := (smallLeftUnstraighteningProjection F).app (Opposite.op ⦋0⦌) d.down
  let x := SSet.opObjEquiv b
  have hx : SSet.opObjEquiv.symm x = b := Equiv.symm_apply_apply _ _
  let p : (vertexFiber (smallLeftUnstraighteningProjection F) (SSet.opObjEquiv.symm x)) _⦋0⦌ :=
    ⟨d.down, hx.symm.trans (pinchedConstant_zero _).symm⟩
  let q := (vertexFiberMap (smallLeftUnstraighteningProjection F)
    (smallLeftUnstraighteningProjection G) m (discreteBaseAction_projection φ)
    (SSet.opObjEquiv.symm x)).app (Opposite.op ⦋0⦌) p
  let s := rightFiberOfLeftPoint F x p
  let t := rightFiberOfLeftPoint G x q
  have hs := rightFiberOfLeftPoint_roundtrip F x p
  have ht := rightFiberOfLeftPoint_roundtrip G x q
  have H := nativeDensityLeg_op_comp φ x (discreteBaseAction_projection φ) s t (by
    rw [hs, ht])
  refine homMk_comp_transfer_of_simplex_eq _
    (edgeOp (densityLegAt F x s).toTruncated) (edgeOp (densityLegAt G x t).toTruncated)
    _ _ ?_ ?_ H
  · exact leftElementsRightKanComparison_leftPoint_edge F x p v f₁ h₁
  · exact leftElementsRightKanComparison_leftPoint_edge G x q v f₀ h₀

end SerrePositivity.InfinityCategories.Sheaves
