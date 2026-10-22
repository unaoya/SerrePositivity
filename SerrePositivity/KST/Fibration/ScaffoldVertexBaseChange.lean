module
public import SerrePositivity.KST.Fibration.ScaffoldReconstructionFiberPoint

/-! # 任意の元の fiber 点に対する、元の底変換成分と scaffold 復元の自然性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

private lemma pointNormalize {C : Type*} [Category C] {a b a' b' z : C}
    (e : a ≅ b) (hs : a = a') (ht : b = b')
    (x : z ⟶ a) (x' : z ⟶ a') (y : z ⟶ b) (y' : z ⟶ b')
    (hx : x ≫ (eqToIso hs).hom = x') (hy : y ≫ (eqToIso ht).hom = y')
    (he : x ≫ e.hom = y) :
    x' ≫ (F2.isoNormalizeEndpoints e hs ht).hom = y' := by
  rw [← hx, ← hy]
  simp only [F2.isoNormalizeEndpoints, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun m => m ≫ (eqToIso ht).hom) he)

variable {E B D : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  [Quasicategory B] (k : D ⟶ B) [Quasicategory D]

local instance : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

omit [Quasicategory B] [Quasicategory D] in
/-- 零単体の第一射影切断の初頂点は、元の指定点の実 fiber 底変換像。 -/
theorem baseChangeZeroSectionFiberPoint_eq (d : D _⦋0⦌)
    (w : (vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    Eq.mp (congrArg (fun b => (vertexFiber p b) _⦋0⦌)
      (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)))
      (firstVertexSectionFiberPoint p ((transportSimplexFunctor k).obj (transportSimplexIndex d))
        (straighteningBaseChangeImageSectionPoint p k (transportSimplexIndex d)
          ((relativeFunctorBaseChangeForward p k (SSet.yonedaEquiv.symm d)).app
            (Opposite.op ⦋0⦌) (vertexFiberZeroSection (pullback.snd p k) d w)))) =
      (cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w := by
  apply Subtype.ext
  have hv := baseChangeImageSectionFiberPoint_val p k (transportSimplexIndex d)
    (vertexFiberZeroSection (pullback.snd p k) d w)
  have hz := congrArg ((pullback.fst p k).app (Opposite.op ⦋0⦌))
    (vertexFiberZeroSection_firstVertex_val (pullback.snd p k) d w)
  exact (vertexFiberPoint_eq_mp_val p
    (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)) _).trans (hv.trans hz)

/-- 元の大域底変換の同じ成分を、元の指定底頂点で表示する。 -/
def scaffoldVertexBaseChangeIso (d : D _⦋0⦌) :=
  F2.isoNormalizeEndpoints (scaffoldBaseChangeCoefficientIso p k (transportSimplexIndex d))
    (congrArg (fun b => HomotopyCategory.mk
      ((leftStraighteningInfinityDiagram p).app (Opposite.op ⦋0⦌) (ULift.up b)))
      (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)))
    (congrArg (fun b => HomotopyCategory.mk
      ((leftStraighteningInfinityDiagram (pullback.snd p k)).app
        (Opposite.op ⦋0⦌) (ULift.up b))) (zeroSimplexFirstVertex d))

omit [Quasicategory B] [Quasicategory D] in
/-- 零単体を通した表示も、元の実図式の同じ指定頂点成分そのもの。 -/
theorem scaffoldVertexBaseChangeIso_eq_diagramValue (d : D _⦋0⦌) :
    scaffoldVertexBaseChangeIso p k d =
      functorIsoValue (leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d) := by
  have hn : HEq (scaffoldVertexBaseChangeIso p k d)
      (scaffoldBaseChangeCoefficientIso p k (transportSimplexIndex d)) := by
    unfold scaffoldVertexBaseChangeIso F2.isoNormalizeEndpoints
    exact F2.iso_endpoints_heq _ _ _
  have hv := F2.vertexIso_map_heq (leftStraighteningInfinityDiagram_baseChangeIso p k)
    (congrArg (fun z : D _⦋0⦌ => evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj D) (Y := SpaceInfinity.{u}) (ULift.up z))
      (zeroSimplexFirstVertex d))
  exact eq_of_heq (hn.trans
    ((scaffoldBaseChangeCoefficientIso_heq_diagramValue p k (transportSimplexIndex d)).trans
      (hv.trans (functorIsoValue_heq_map
        (leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d)).symm)))

/-- 元の fiber 点の第一射影による復元像は、元の底変換比較で同じ pullback 復元像へ送られる。 -/
theorem scaffoldVertexBaseChangeIso_pointHom (d : D _⦋0⦌)
    (w : (vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p (k.app (Opposite.op ⦋0⦌) d)
      ((cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w)) ≫
        (scaffoldVertexBaseChangeIso p k d).hom =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint (pullback.snd p k) d w) := by
  let v := vertexFiberZeroSection (pullback.snd p k) d w
  let c := transportSimplexIndex d
  have hs := scaffoldReconstructionFiberPoint_eq_transport p
    (zeroSimplexFirstVertex (k.app (Opposite.op ⦋0⦌) d)) _ _
    (baseChangeZeroSectionFiberPoint_eq p k d w)
  have ht := scaffoldReconstructionFiberPoint_eq_transport (pullback.snd p k)
    (zeroSimplexFirstVertex d) _ w (vertexFiberZeroSection_firstVertex (pullback.snd p k) d w)
  have he := scaffoldBaseChangeCoefficientIso_pointHom p k c v
  exact pointNormalize _ _ _ _ _ _ _ hs ht he

/-- 任意の元の fiber 点について、復元の実像は元の図式の底変換成分と両立する。 -/
theorem scaffoldPointedReconstruction_baseChange_pointHom (d : D _⦋0⦌)
    (w : (vertexFiber (pullback.snd p k) d) _⦋0⦌) :
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p (k.app (Opposite.op ⦋0⦌) d)
      ((cofinalVertexFiberBaseChangeIso p k d).hom.app (Opposite.op ⦋0⦌) w)) ≫
      (functorIsoValue (leftStraighteningInfinityDiagram_baseChangeIso p k) (ULift.up d)).hom =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint (pullback.snd p k) d w) := by
  rw [← scaffoldVertexBaseChangeIso_eq_diagramValue p k d]
  exact scaffoldVertexBaseChangeIso_pointHom p k d w

end SerrePositivity.KST.Fibration
