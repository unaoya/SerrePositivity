module
public import SerrePositivity.InfinityCategories.Derived.DGHomTargetTransportRepresentation
public import SerrePositivity.InfinityCategories.Derived.DGModuleUnderlyingCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGClosedCosliceTransport
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomQuasiIso
/-!
概要：全 Hom 後合成の準同型性を同じ空間値 Hom 関手の実辺の可逆性へ昇格する。
方針：同じ実 coslice 輸送と pointed 全空間の比較を使う。
規約：生の終点の射影性は不要。使われ方：一般 tensor–Hom の ∞ 随伴への準備。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C]
/-- 同じ全 Hom 関手と実辺による比較。 -/
lemma dgHomTargetUnderlyingSpaceInfinity_invertsPostcomposition
    (x y z : C)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    [QuasiIso (dgClosedPostcomposition R C (x := x) f)] :
    IsInvertibleEdge ((SSet.Edge.ofTruncated
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (dgClosedEdge R C f))).map (dgHomTargetUnderlyingSpaceInfinity R C x)) := by
  let p := sliceUnderProjection
    ((SSet.yonedaEquiv (X := dgNerve R C)).symm (Simplex.vertex x))
  let e := SSet.Edge.ofTruncated (X := dgNerve R C) (dgClosedEdge R C f)
  have he := dgClosedCosliceTransport_isQCatEquivalence R C x y z f
  have hu := dgEdgeTransport_ulift_isQCatEquivalence.{max (u + 1) v,
    max (u + 1) v + 1} p e he
  have ht := (dgLeftFibrationSquareTransport_isQCatEquivalence_iff
    ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map p) pointedSpaceProjection
    (dgHomTargetCoslicePointedDisplay R C x) (dgHomTargetUnderlyingSpaceInfinity R C x)
    (dgHomTargetCoslicePointedDisplay_projection R C x)
    (SSet.Edge.ofTruncated (uliftTruncatedEdge.{max (u + 1) v,
      max (u + 1) v + 1} (dgClosedEdge R C f)))
    (dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x (Simplex.vertex y))
    (dgHomTargetCoslicePointedDisplay_fiber_isQCatEquivalence R C x (Simplex.vertex z))).mp hu
  exact pointedSpaceEdge_isInvertible_of_transport_isQCatEquivalence _ ht
/-- 同じ全 Hom 関手と実辺による比較。 -/
lemma dgModuleHomTargetUnderlyingSpaceInfinity_invertsQuasiIso
    (D : Type v) [DGCategory R D] [Small.{u} D] (T : RightModule R D)
    (hT : moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R) T))
    {M N : RightModule R D}
    (f : ForgetEnrichment.of (Complex R) M ⟶ ForgetEnrichment.of (Complex R) N)
    (hf : moduleQuasiIso R D f) :
    IsInvertibleEdge ((SSet.Edge.ofTruncated
      (uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v + 1}
        (dgClosedEdge R (RightModule R D) f))).map
      (dgHomTargetUnderlyingSpaceInfinity R (RightModule R D) T)) := by
  let : QuasiIso (dgClosedPostcomposition R (RightModule R D) (x := T) f) :=
    moduleHomotopicallyProjective_postcompose_quasiIso R D hT f hf
  exact dgHomTargetUnderlyingSpaceInfinity_invertsPostcomposition R (RightModule R D) T M N f
end SerrePositivity.InfinityCategories
