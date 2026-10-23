module
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingSpacePointed
public import SerrePositivity.InfinityCategories.F1.Universe.Transport
public import SerrePositivity.InfinityCategories.F1.Universe.Reflection
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationTransportNaturality
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationFiberReflection
/-!
概要：基礎空間関手の実辺の可逆性を、元の同じ coslice 輸送の同値性で判定する。
方針：宇宙持ち上げの実輸送比較と coslice から始点固定 Tw への全 fiber 同値を使う。
規約：点ごとの空間同値だけでは判定しない。使われ方：実 augmentation の像の可逆性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet
open scoped Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
/-- 実 left-fibration 輸送の同値性は、同じ宇宙持ち上げた実輸送でも保たれる。 -/
lemma dgEdgeTransport_ulift_isQCatEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌} (e : SSet.Edge a b)
    (he : IsQCatEquivalence (edgeTransport p e)) :
    IsQCatEquivalence (edgeTransport ((SSet.uliftFunctor.{v, u}).map p)
      (uliftTruncatedEdge.{u, v} e)) := by
  have hu := (isQCatEquivalence_ulift_iff_of_kan.{u, v} (edgeTransport p e)).mpr he
  have ha := (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, v} p a).symm).isQCatEquivalence
  have hb := (qCatEquivalenceOfIso (uliftVertexFiberIso.{u, v} p b)).isQCatEquivalence
  have H : IsQCatEquivalence (uliftFiberTransport.{u, v} p (edgeTransport p e)) :=
    ha.comp (hu.comp hb)
  exact H.ofFunctorIso (edgeTransport_uliftIso.{u, v} p e).symm
variable (R : Type u) [CommRing R] (D : Type v)
/-- 元の coslice 輸送が同値なら、同じ基礎空間関手で写した実辺は可逆。 -/
lemma dgHomUnderlyingSpaceInfinity_invertible_of_cosliceTransport
    {y z : (dgHomModuleNerve R D) _⦋0⦌} (e : SSet.Edge y z)
    (he : IsQCatEquivalence (edgeTransport
      (sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R D))) e)) :
    IsInvertibleEdge ((SSet.Edge.ofTruncated
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1} e)).map
        (dgHomUnderlyingSpaceInfinity R D)) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm (dgHomModuleUnitVertex R D))
  let q := twistedArrowSourceProjection (dgHomModuleUnitVertex R D)
  let f := cosliceToTwistedArrowSource (dgHomModuleUnitVertex R D)
  have hf : f ≫ q = p := cosliceToTwistedArrowSource_projection _
  have hF (b : (dgHomModuleNerve R D) _⦋0⦌) :
      IsQCatEquivalence (vertexFiberMap p q f hf b) :=
    vertexFiberMap_isQCatEquivalence_of_precompositionEquivalence p q f hf
      (cosliceToTwistedArrowSource_isPrecompositionEquivalence _) b
  have ht := (leftFibrationMap_transport_isQCatEquivalence_iff p q f hf e (hF y) (hF z)).mp he
  have hU := dgEdgeTransport_ulift_isQCatEquivalence.{max (u + 1) v, max (u + 1) v + 1} q e ht
  exact dgHomUnderlyingSpaceInfinity_invertible_of_sourceTransport R D
    (SSet.Edge.ofTruncated (uliftTruncatedEdge e)) hU
end SerrePositivity.InfinityCategories
