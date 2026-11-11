module

public import SerrePositivity.EInfinity.Interface.Theory
public import SerrePositivity.EInfinity.ComplexLimits.DerivedSourceValues
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyNaturality
public import SerrePositivity.InfinityCategories.Derived.DGStableHomotopyEdges
public import SerrePositivity.InfinityCategories.F1B.HomotopyEdgeNaturality

/-!
# 通常複体の導来像のホモロジー

## 概要
BS 著者版 Theorem 6.2 の Tot で用いる、厳密複体とその導来像の全次数の比較。

## 方針
既存の半自由分解の全 augmentation にホモロジーを適用する。

## 規約
同じ分解の射と自然性を保持し、複体には有界性を課さない。

## 使われ方
Barratt–Eccles 実例の `strictToD_homologyIso`。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory SSet SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open DGNerve DGNerve.HomotopyComparison
open scoped Simplicial

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- 通常複体の dg nerve 上で閉零辺をホモロジー写像へ送る関手。 -/
def ambientCohomology (i : ℤ) :
    (dgNerve A (Complex A)).HomotopyCategory ⥤ ModuleCat.{u} A :=
  (dgStableHomotopyEquivalence A (Complex A)).functor ⋙ complexHomotopyComparison A ⋙
    _root_.HomotopyCategory.homologyFunctor (ModuleCat A) (.up ℤ) i

/-- 閉零の頂点表示と元の複体との比較。 -/
def ambientCohomologyVertexIso (i : ℤ) (x : (dgNerve A (Complex A)) _⦋0⦌) :
    (ambientCohomology A i).obj (SSet.HomotopyCategory.mk x) ≅ (x.obj 0).homology i :=
  (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat A) (.up ℤ) i).app (x.obj 0)

lemma ambientCohomology_map (i : ℤ) {x y : (dgNerve A (Complex A)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A (Complex A))) x y) :
    (ambientCohomology A i).map (Truncated.HomotopyCategory.homMk e) ≫
      (ambientCohomologyVertexIso A i y).hom =
    (ambientCohomologyVertexIso A i x).hom ≫
      HomologicalComplex.homologyMap ((closedToComplex A).map (edgeClosed e)) i := by
  let H := _root_.HomotopyCategory.homologyFunctor (ModuleCat A) (.up ℤ) i
  let Q := _root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)
  let f := edgeClosed e
  have h := Functor.congr_hom (complexHomotopyComparison_fac A) f
  change (complexHomotopyComparison A).map ((toHomotopy A (Complex A)).map f) =
    Q.map ((closedToComplex A).map f) at h
  change H.map ((complexHomotopyComparison A).map
    ((dgStableHomotopyEquivalence A (Complex A)).functor.map
      (Truncated.HomotopyCategory.homMk e))) ≫ _ = _
  rw [dgStableHomotopyEquivalence_map_homMk, h]
  exact (_root_.HomotopyCategory.homologyFunctorFactors (ModuleCat A) (.up ℤ) i).hom.naturality
    ((closedToComplex A).map f)

/-- Theorem 6.2 の比較に用いる、半自由包含のホモロジーとの自然同型。 -/
def derivedAmbientCohomologyIso (i : ℤ) :
    cohomologyOnHo A i ≅ hoMap (derivedInfinityInclusion (S := A)) ⋙ ambientCohomology A i := by
  let I := dgFullSubcategoryInclusion A (Complex A) (complexSemifree A)
  exact Functor.isoWhiskerLeft (homotopyCategoryBridge (derivedInfinityCategory A)).inverse
    (derivedInfinityHomologyComparison A i) ≪≫
    Functor.isoWhiskerRight (dgStableHomotopyEquivalence_naturalityIso A _ _ I).symm
      (complexHomotopyComparison A ⋙ _root_.HomotopyCategory.homologyFunctor
        (ModuleCat A) (.up ℤ) i)

/-- 一単体が同じ二辺の閉零射は、端点の表示を含めて一致する。 -/
lemma chainMap_heq_of_edge_eq
    {x y x' y' : (dgNerve A (Complex A)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A (Complex A))) x y)
    (e' : Truncated.Edge (X := (truncation 2).obj (dgNerve A (Complex A))) x' y')
    (h : e.edge = e'.edge) :
    HEq ((closedToComplex A).map (edgeClosed e))
      ((closedToComplex A).map (edgeClosed e')) := by
  have hx : x = x' := e.src_eq.symm.trans
    ((congrArg (fun s => (dgNerve A (Complex A)).δ 1 s) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans
    ((congrArg (fun s => (dgNerve A (Complex A)).δ 0 s) h).trans e'.tgt_eq)
  subst x'
  subst y'
  rw [(Truncated.Edge.ext h : e = e')]

private lemma quasiIso_closed_of_edge_eq
    {x y x' y' : (dgNerve A (Complex A)) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (dgNerve A (Complex A))) x y)
    (e' : Truncated.Edge (X := (truncation 2).obj (dgNerve A (Complex A))) x' y')
    (h : e.edge = e'.edge) :
    QuasiIso ((closedToComplex A).map (edgeClosed e)) ↔
      QuasiIso ((closedToComplex A).map (edgeClosed e')) := by
  have hx : x = x' := e.src_eq.symm.trans
    ((congrArg (fun s => (dgNerve A (Complex A)).δ 1 s) h).trans e'.src_eq)
  have hy : y = y' := e.tgt_eq.symm.trans
    ((congrArg (fun s => (dgNerve A (Complex A)).δ 0 s) h).trans e'.tgt_eq)
  subst x'
  subst y'
  rw [(Truncated.Edge.ext h : e = e')]

/-- 同じ解像の全 augmentation の各辺は擬同型。 -/
lemma complexSemifreeResolutionAugmentation_edge_quasiIso
    (x : (dgNerve A (Complex A)) _⦋0⦌) :
    QuasiIso ((closedToComplex A).map (edgeClosed (simplicialHomotopyVertexEdge
      (complexSemifreeResolutionAugmentationHomotopy A) x).toTruncated)) := by
  obtain ⟨X, rfl⟩ := (Simplex.vertexEquiv (A := A) (D := Complex A)).symm.surjective x
  let F := ringConstantDG A
  let Q := dgModuleOutputResolutionObject A (Complex A) PUnit.{1} F X
  let G := moduleEvaluationDG A PUnit.{1} PUnit.unit
  let e := (dgClosedEdge A (RightModule A PUnit.{1}) Q.augmentation).map
    ((truncation 2).map (dgNerve.map G))
  apply (quasiIso_closed_of_edge_eq A _ e ?_).mpr
  · rw [dgNerveEdgeClosed_map, dgClosedEdge_closed]
    exact Q.quasiIso PUnit.unit
  · change (dgNerve.map G).app (Opposite.op ⦋1⦌)
      (simplicialHomotopyVertexEdge (dgModuleResolvedAugmentationHomotopy A
        (Complex A) PUnit.{1} F) (Simplex.vertex X)).edge = _
    rw [dgModuleResolvedAugmentationHomotopy_vertex_edge]
    rfl

/-- 半自由解像を取っても全 dg 複体のホモロジー関手は変わらない。 -/
def complexResolutionCohomologyIso (i : ℤ) :
    hoMap (complexSemifreeResolutionInfinity A) ⋙ cohomologyOnHo A i ≅
      ambientCohomology A i := by
  let L := complexSemifreeResolutionInfinity A
  let I := derivedInfinityInclusion (S := A)
  let H := complexSemifreeResolutionAugmentationHomotopy A
  let η := homotopyNatTransOfEndpoints H.h H.h₀ H.h₁
  let α := Functor.whiskerRight η (ambientCohomology A i)
  haveI (x : (dgNerve A (Complex A)).HomotopyCategory) : IsIso (α.app x) := by
    induction x using SSet.HomotopyCategory.rec with
    | mk x =>
      change IsIso ((ambientCohomology A i).map (η.app (SSet.HomotopyCategory.mk x)))
      rw [F2.homotopyNatTransOfEndpoints_app]
      let e := (simplicialHomotopyVertexEdge H x).toTruncated
      let s := ambientCohomologyVertexIso A i (atVertex (L ≫ I) x)
      let t := ambientCohomologyVertexIso A i x
      let f := HomologicalComplex.homologyMap ((closedToComplex A).map (edgeClosed e)) i
      have hq := complexSemifreeResolutionAugmentation_edge_quasiIso A x
      have : IsIso f := (quasiIsoAt_iff_isIso_homologyMap _ _).mp (hq.quasiIsoAt i)
      have h : (ambientCohomology A i).map (Truncated.HomotopyCategory.homMk e) =
          s.hom ≫ f ≫ t.inv := by
        have h := ambientCohomology_map A i e
        change (ambientCohomology A i).map (Truncated.HomotopyCategory.homMk e) ≫
          t.hom = s.hom ≫ f at h
        simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
          congrArg (fun k => k ≫ t.inv) h
      rw [h]
      infer_instance
  letI : IsIso α := NatIso.isIso_of_isIso_app α
  have e : hoMap (L ≫ I) ≅ hoMap L ⋙ hoMap I := eqToIso (by
    change (hoFunctor.map (L ≫ I)).toFunctor = _
    rw [hoFunctor.map_comp]
    rfl)
  have eId : hoMap (𝟙 (dgNerve A (Complex A))) ≅ 𝟭 _ :=
    eqToIso (by
      change (hoFunctor.map (𝟙 (dgNerve A (Complex A)))).toFunctor = _
      rw [hoFunctor.map_id]
      rfl)
  exact Functor.isoWhiskerLeft (hoMap L) (derivedAmbientCohomologyIso A i) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.symm _ ≪≫
    asIso α ≪≫ Functor.isoWhiskerRight eId _ ≪≫ Functor.leftUnitor _

/-- Theorem 6.2 の厳密複体を D(A) に送る際の全次数の自然比較。 -/
def complexOrdinaryDerivedSourceHomologyIso (i : ℤ) :
    ordinaryToHoNerve (Complex A) ⋙ hoMap (complexOrdinaryDerivedSource A) ⋙ cohomologyOnHo A i ≅
      HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i := by
  let B := nerveMap (complexToClosed A) ≫ closedNerveInclusion A (Complex A)
  let L := complexSemifreeResolutionInfinity A
  have e₁ : hoMap (complexOrdinaryDerivedSource A) ≅ hoMap B ⋙ hoMap L := by
    apply eqToIso
    change (hoFunctor.map (nerveMap (complexToClosed A) ≫
      closedNerveInclusion A (Complex A) ≫ L)).toFunctor = _
    rw [← Category.assoc, hoFunctor.map_comp]
    rfl
  have e₂ : ordinaryToHoNerve (Complex A) ⋙ hoMap B ⋙ ambientCohomology A i ≅
      HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) i := by
    refine NatIso.ofComponents
      (fun X => ambientCohomologyVertexIso A i (atVertex B (nerveVertex X))) ?_
    intro X Y f
    change (ambientCohomology A i).map
      (Truncated.HomotopyCategory.homMk (((nerve.edgeMk f).map B).toTruncated)) ≫ _ = _
    let e := ((nerve.edgeMk f).map B).toTruncated
    have he : (((nerve.edgeMk f).map B).toTruncated).edge =
        (dgClosedEdge A (Complex A) ((complexToClosed A).map f)).edge := by
      change B.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f) = _
      simp only [B, NatTrans.comp_app_apply, nerveMap_app_mk₁, closedNerveInclusion_mk₁]
    have hf : (closedToComplex A).map (edgeClosed e) = f := by
      have h := chainMap_heq_of_edge_eq A e
        (dgClosedEdge A (Complex A) ((complexToClosed A).map f)) he
      rw [dgClosedEdge_closed, complexToClosed_map A f] at h
      exact eq_of_heq h
    exact (ambientCohomology_map A i e).trans (by rw [hf]; rfl)
  exact Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight e₁ _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (complexResolutionCohomologyIso A i)) ≪≫ e₂

end SerrePositivity.EInfinity.ComplexLimits
