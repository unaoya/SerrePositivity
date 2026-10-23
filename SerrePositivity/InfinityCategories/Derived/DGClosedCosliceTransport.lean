module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentClosedEdges
public import SerrePositivity.InfinityCategories.Derived.DGCoherentSliceComparison
public import SerrePositivity.InfinityCategories.Derived.DGPointCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGCoherentCosliceTransport
public import SerrePositivity.InfinityCategories.Derived.DGStandardClosedPostcomposition
public import SerrePositivity.InfinityCategories.DoldKanComparison.ComparisonEquivalence
public import SerrePositivity.InfinityCategories.F1.Transport.UniversalTransportReflection
/-!
概要：全 Hom の閉後合成の準同型性から、元の dg nerve の実 coslice 輸送の同値性を得る。
方針：同じ DK 後合成を coherent 輸送へ送り、充満忠実な同じ比較射と実辺の一致で戻す。
規約：前三角性も対象の小ささも不要。使われ方：R の代表加群からの実 augmentation の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DoldKanComparison SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
/-- 全 Hom の同じ閉後合成が準同型なら、その dg 実辺の coslice 輸送は全空間同値。 -/
lemma dgClosedCosliceTransport_isQCatEquivalence (x y z : D)
    (f : ForgetEnrichment.of (Complex R) y ⟶ ForgetEnrichment.of (Complex R) z)
    [QuasiIso (dgClosedPostcomposition R D (x := x) f)] :
    IsQCatEquivalence (edgeTransport (B := dgNerve R D)
      (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x)))
      (dgClosedEdge R D f)) := by
  let : Quasicategory (SimplicialNerve (ClosedCategory R D)) :=
    Coherent.simplicialNerve_quasicategory (ClosedCategory R D)
  have hC := dgCoherentCosliceTransport_isQCatEquivalence_of_sHom
    (ForgetEnrichment.of (Complex R) x) f
    (dgStandardSimplicialPostcomp_isQCatEquivalence R D x y z f)
  have H := (dgPointCosliceTransport_equivalence_iff
    (coherentComparison (R := R) (D := D))
    (coherentNerveVertex (ForgetEnrichment.of (Complex R) x))
    (coherentComparison_fullyFaithful (R := R) (D := D)) (coherentNerveEdge f)).mp hC
  have hx := congrArg SSet.yonedaEquiv (dgCoherentTargetPoint R D x)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at hx
  erw [hx] at H
  exact (edgeTransport_isQCatEquivalence_congr_edge
    (sliceUnderProjection ((SSet.yonedaEquiv (X := dgNerve R D)).symm (Simplex.vertex x)))
    ((coherentNerveEdge f).map (coherentComparison (R := R) (D := D)))
    (SSet.Edge.ofTruncated (dgClosedEdge R D f))
    (dgCoherentComparison_closed_edge R D _ _ f)).mp H
end SerrePositivity.InfinityCategories
