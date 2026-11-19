module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallUnstraighteningPointedActionBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.DensityLegEvaluatedTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CanonicalYonedaFiberTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointedTransformationPointHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberHomClass
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.IntervalIsoHomClass

/-!
概要：元の密度脚の合成を Yoneda の恒等点で検出し、指定底変換の作用と照合する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open CategoryTheory Limits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

private theorem yoneda_homMk_eq_of_identity_pointHom_eq
    {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
    (e g : (PresheafInfinity C).Edge
      (functorVertex (representablePresheafInfinity x)) (functorVertex F)) :
    let b := ULift.up (SSet.opObjEquiv.symm x)
    let q := canonicalYonedaPointedIdentity x
    cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk (functorEdgeAt e b).toTruncated =
      cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk (functorEdgeAt g b).toTruncated →
    Truncated.HomotopyCategory.homMk e.toTruncated = Truncated.HomotopyCategory.homMk g.toTruncated := by
  intro b q h
  let R := representablePresheafInfinity x
  let v := intervalMappingVertexOfEdge e
  let w := intervalMappingVertexOfEdge g
  let M := canonicalYonedaTransformationFiberEvaluation x F
  have hv (f : (PresheafInfinity C).Edge (functorVertex R) (functorVertex F)) :
      cosliceFiberPointHom q ≫
        Truncated.HomotopyCategory.homMk (functorEdgeAt f b).toTruncated =
      cosliceFiberPointHom (M.app (Opposite.op ⦋0⦌) (intervalMappingVertexOfEdge f)) := by
    have hh := pointedTransformationPointHom R F (intervalMappingVertexOfEdge f) b q
    have hf : intervalMappingEdgeOfVertex (intervalMappingVertexOfEdge f) = f :=
      (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply f
    rw [hf] at hh
    exact hh
  have hcl : cosliceFiberPointHom (M.app (Opposite.op ⦋0⦌) v) =
      cosliceFiberPointHom (M.app (Opposite.op ⦋0⦌) w) := (hv e).symm.trans (h.trans (hv g))
  let cl := cosliceFiberVertexIsoOfHomEq hcl
  let u := (canonicalYonedaTransformationFiberEvaluation_isQCatEquivalence x F).isFullyFaithful
    |>.preimageVertexIso cl
  have H := intervalRecoveredHom_eq_of_vertexIso u
  have he : intervalMappingEdgeOfVertex v = e :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply e
  have hg : intervalMappingEdgeOfVertex w = g :=
    (intervalMappingEdgeVertexEquiv _ _).symm_apply_apply g
  rwa [he, hg] at H


private theorem yoneda_homMk_comp_of_identity_pointHom_eq
    {C : SSet.{u}} [Quasicategory C]
    (F G : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
    (l : (PresheafInfinity C).Edge
      (functorVertex (representablePresheafInfinity x)) (functorVertex F))
    (a : (PresheafInfinity C).Edge (functorVertex F) (functorVertex G))
    (r : (PresheafInfinity C).Edge
      (functorVertex (representablePresheafInfinity x)) (functorVertex G)) :
    let b := ULift.up (SSet.opObjEquiv.symm x)
    let q := canonicalYonedaPointedIdentity x
    (cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk (functorEdgeAt l b).toTruncated) ≫
        Truncated.HomotopyCategory.homMk (functorEdgeAt a b).toTruncated =
      cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk (functorEdgeAt r b).toTruncated →
    Truncated.HomotopyCategory.homMk l.toTruncated ≫
      Truncated.HomotopyCategory.homMk a.toTruncated =
      Truncated.HomotopyCategory.homMk r.toTruncated := by
  intro b q h
  obtain ⟨k, hk⟩ := homotopyCategory_homMk_surjective
    (functorVertex (representablePresheafInfinity x)) (functorVertex G)
    (Truncated.HomotopyCategory.homMk l.toTruncated ≫
      Truncated.HomotopyCategory.homMk a.toTruncated)
  let e := SSet.Edge.ofTruncated (X := PresheafInfinity C) k
  have he : Truncated.HomotopyCategory.homMk e.toTruncated =
      Truncated.HomotopyCategory.homMk l.toTruncated ≫
        Truncated.HomotopyCategory.homMk a.toTruncated := hk
  have hEval : Truncated.HomotopyCategory.homMk (functorEdgeAt e b).toTruncated =
      Truncated.HomotopyCategory.homMk (functorEdgeAt l b).toTruncated ≫
        Truncated.HomotopyCategory.homMk (functorEdgeAt a b).toTruncated := by
    rw [← functorHomEvaluate_edge_hom, ← functorHomEvaluate_edge_hom,
      ← functorHomEvaluate_edge_hom, he, functorHomEvaluate_comp]
  have hp : cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk
      (functorEdgeAt e b).toTruncated =
      cosliceFiberPointHom q ≫ Truncated.HomotopyCategory.homMk (functorEdgeAt r b).toTruncated := by
    rw [hEval, ← Category.assoc]
    exact h
  exact he.symm.trans (yoneda_homMk_eq_of_identity_pointHom_eq G x e r hp)


def densityLegAt
    {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    (PresheafInfinity C).Edge (functorVertex (representablePresheafInfinity x)) (functorVertex F) :=
  (coconeVertexLeg (presheafDensityCocone F) (ULift.up s.val)).ofEq
    (by
      have h : (smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) s.val = x :=
        s.property.trans (pinchedConstant_zero x)
      change (yonedaInfinityMap C).app (Opposite.op ⦋0⦌)
        (ULift.up ((smallRightUnstraighteningProjection F).app (Opposite.op ⦋0⦌) s.val)) = _
      rw [h, yonedaInfinityMap_vertex])
    (presheafDensityCocone_vertex F)

private theorem densityLegAt_pointHom
    {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
    (s : (vertexFiber (smallRightUnstraighteningProjection F) x) _⦋0⦌) :
    let b := SSet.opObjEquiv.symm x
    let j := canonicalYonedaPointedIdentity x
    let l := functorEdgeAt (densityLegAt F x s) (ULift.up b)
    let v := (presheafRightFiberLeftIso F x).hom.app _ (SSet.opObjEquiv.symm s)
    cosliceFiberPointHom j ≫ Truncated.HomotopyCategory.homMk l.toTruncated =
      cosliceFiberPointHom (smallUnstraighteningPointedImage F b v) := by
  intro b j l v
  obtain ⟨h⟩ := presheafDensityLeg_evaluatedTransport F x s
  exact (cosliceTransportPointHom l (edgeTransport pointedSpaceProjection l)
    (edgeTransport_isTransport pointedSpaceProjection l) j).trans
    (cosliceFiberPointHom_eq_of_vertexIso h)

/-- 元の密度脚の合成を Yoneda の恒等点で検出し、指定底変換の作用と照合する。
Kerodon §8.3 の Yoneda と §9.3（Tag 06FR）の密度比較。HTT 5.1.5.6。 -/
lemma densityLegAt_baseAction_comp
    {C D : SSet.{u}} [Quasicategory C] (i : C.op ≅ D)
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj D ⟶ SpaceInfinity.{u}}
    (a : FunctorHom F G) (x : C _⦋0⦌) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let F' := U.map i.hom ≫ F
    let G' := U.map i.hom ≫ G
    let L := smallLeftUnstraighteningBaseIso i F
    let R := smallLeftUnstraighteningBaseIso i G
    let m := L.hom ≫ smallUnstraighteningFunctorHom a ≫ R.inv
    let b := SSet.opObjEquiv.symm x
    ∀ (hm : m ≫ smallLeftUnstraighteningProjection G' = smallLeftUnstraighteningProjection F')
      (s : (vertexFiber (smallRightUnstraighteningProjection F') x) _⦋0⦌)
      (t : (vertexFiber (smallRightUnstraighteningProjection G') x) _⦋0⦌)
      (g : (PresheafInfinity C).Edge (functorVertex F') (functorVertex G')),
    let p := (presheafRightFiberLeftIso F' x).hom.app _ (SSet.opObjEquiv.symm s)
    let q := (presheafRightFiberLeftIso G' x).hom.app _ (SSet.opObjEquiv.symm t)
    (vertexFiberMap (smallLeftUnstraighteningProjection F') (smallLeftUnstraighteningProjection G')
      m hm b).app _ p = q →
    Truncated.HomotopyCategory.homMk (functorEdgeAt g (ULift.up b)).toTruncated =
      functorHomEvaluate a (ULift.up (i.hom.app (Opposite.op ⦋0⦌) b)) →
    Truncated.HomotopyCategory.homMk (densityLegAt F' x s).toTruncated ≫
        Truncated.HomotopyCategory.homMk g.toTruncated =
      Truncated.HomotopyCategory.homMk (densityLegAt G' x t).toTruncated := by
  intro U F' G' L R m b hm s t g p q hp hg
  apply yoneda_homMk_comp_of_identity_pointHom_eq F' G' x (densityLegAt F' x s) g
    (densityLegAt G' x t)
  rw [densityLegAt_pointHom, densityLegAt_pointHom, hg]
  let h := smallUnstraighteningPointedBase_action i a b hm p
  dsimp only at h
  rw [hp] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
