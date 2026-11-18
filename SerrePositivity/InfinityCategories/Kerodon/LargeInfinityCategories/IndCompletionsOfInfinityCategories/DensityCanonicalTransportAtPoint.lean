module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityCanonicalTransportEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrowEdgeComposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.UniverseVertexIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointAction

/-!
概要：元の密度の指定区間を恒等点で輸送した終値は、同じ要素の小さい left fiber の pointed 値と同型。
方針：元の大域切断の恒等 fiber の辺と pointed 終値を保持する。
使われ方：離散前層の密度の脚の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

private theorem twistedIdentityFiberEvaluation_point
    {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p] (x : B _⦋0⦌)
    (s : (vertexFiber p x) _⦋0⦌) :
    Nonempty (VertexIso ((twistedIdentityFiberEvaluation p x).app _ s)
      (SSet.opObjEquiv.symm s)) := by
  let A := vertexFiber p x
  let v := (twistedIdentityFiberLift p x).app (Opposite.op ⦋0⦌) s
  let e := twistedArrowVertexEdge v
  have hr : (edgewiseRight A).app _ v = s := by
    let ev (f : A ⟶ A) : A _⦋0⦌ := f.app (Opposite.op ⦋0⦌) s
    exact congrArg ev (twistedIdentityFiberLift_right p x)
  let rev₀ := SSet.Edge.ofTruncated (X := A.op) (edgeOp e.toTruncated)
  let rev := (rev₀.ofEq (congrArg SSet.opObjEquiv.symm hr)
    (SSet.opObjEquiv.symm_apply_apply _)).toTruncated
  have hA : KanComplex A := vertexFiber_kanComplex p x
  have hOp : KanComplex A.op := inferInstance
  have hIso : IsIso (Truncated.HomotopyCategory.homMk rev) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj A.op) _
  exact ⟨(asIso (Truncated.HomotopyCategory.homMk rev)).symm⟩

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "z" => presheafDensityEvaluationVertex F x

private noncomputable def densityIdentityEndpoint_valueIso :
    FunctorIso
      (presheafDensityIdentityLiftEndpoint F x ≫ (pointedSpaceFiberValueEquivalence z).hom)
      ((SSet.uliftFunctor.{u + 1, u}).map (twistedIdentityFiberEvaluation p x) ≫
        (presheafRightFiberPointedIso F x).hom ≫ (pointedSpaceFiberValueEquivalence z).hom) := by
  rw [presheafDensityIdentityLiftEndpoint_value]
  let r := presheafDensityIdentityReconstruction F x
  have h₀ := (presheafDensityEvaluationFiberIso F x).precomp r
  have h₁ := presheafDensityNativeIdentityValueIso F x
  have h₂ : presheafDensityIdentityValue F x =
      (SSet.uliftFunctor.{u + 1, u}).map (twistedIdentityFiberEvaluation p x) ≫
        (presheafRightFiberPointedIso F x).hom ≫ (pointedSpaceFiberValueEquivalence z).hom := by
    rw [presheafDensityIdentityValue_factorization, Functor.map_comp,
      presheafRightFiberValueEquivalence_lift]
  rw [h₂] at h₁
  exact h₀.symm ≪≫ h₁

/-- 元の密度の指定区間を恒等点で輸送した終値は、同じ要素の小さい left fiber の pointed 値と同型。
Kerodon §9.3（Tag 06FR）の密度比較。HTT 5.1.5.6 に使う恒等点での照合。 -/
lemma densityCanonicalTransport_at_native_point
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    let b := SSet.opObjEquiv.symm x
    let a := presheafDensityCanonicalSourceValue x
    let z₀ := F.app (Opposite.op ⦋0⦌) (ULift.up b)
    let e := presheafDensityCanonicalFiberInterval F x ≫
      parametrizedFiberTransport pointedSpaceProjection a z₀ ≫
        evaluateFunctorAt (canonicalYonedaPointedIdentity x)
    let v := smallUnstraighteningPointedImage F b
      ((presheafRightFiberLeftIso F x).hom.app _ (SSet.opObjEquiv.symm s))
    Nonempty (VertexIso (e.app _ (ULift.up s)) v) := by
  intro b a z₀ e v
  let M := pointedSpaceFiberValueEquivalence z
  let E := presheafDensityIdentityLiftEndpoint F x
  let D := presheafRightFiberPointedIso F x
  have hs := densityIdentityEndpoint_valueIso F x
  have hAt := VertexIso.map hs (evaluateFunctorAt (ULift.up s))
  simp only [evaluateFunctorAt_functorVertex, NatTrans.comp_app, ConcreteCategory.comp_apply] at hAt
  let hLift := M.isQCatEquivalence.isFullyFaithful.preimageVertexIso hAt
  obtain ⟨hTw⟩ := twistedIdentityFiberEvaluation_point p x s
  have hF : KanComplex (vertexFiber p x) := vertexFiber_kanComplex p x
  let hD := (uliftVertexIso hTw).map D.hom
  let j := eqToHom (congrArg (vertexFiber pointedSpaceProjection)
    (presheafDensityEvaluationVertex_value F x))
  have hEndpoint := VertexIso.map (presheafDensityIdentityLiftEndpointTransportIso F x)
    (evaluateFunctorAt (ULift.up s))
  simp only [evaluateFunctorAt_functorVertex] at hEndpoint
  -- Transport the two fixed-endpoint comparisons along the same normalization.
  let L := smallLeftUnstraighteningFiberIso F b ≪≫ leftUnstraighteningFiberIso F (ULift.up b)
  let R := (SSet.uliftFunctor.{u + 1, u}).mapIso (presheafRightFiberLeftIso F x)
  have hj : D.hom ≫ j = R.hom ≫ L.hom := by
    simp only [b, D, j, R, L, presheafRightFiberPointedIso, Iso.trans_hom, eqToIso.hom,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hv : j.app _ (D.hom.app _ (ULift.up (SSet.opObjEquiv.symm s))) = v := by
    exact congrArg (fun k => k.app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm s))) hj
  exact ⟨hEndpoint.symm ≪≫ VertexIso.map (hLift ≪≫ hD) j ≪≫
    eqToIso (congrArg HomotopyCategory.mk hv)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
