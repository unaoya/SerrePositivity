module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackThickImage
/-!
概要：元の通常 pullback 包含は同じ平坦商の零対象核であり、その本質像に沿う辺で局所化する。
方針：D-16 の核反映と局所化の両欄を実 thick 核の本質像の一致で移す。
規約：元の包含と同じ cell 平坦商を保持する。
使われ方：Sp の IsVerdierSequence の kernel・quotient 欄を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (hC : IsDGPretriangulated R C) (hD : IsDGPretriangulated R D)
include hC hD
lemma dgGluingPullbackFlatQuotient_zero_iff
    (b : (dgNerve R (DGGluingObject R C D M)) _⦋0⦌) :
    IsZeroVertex ((dgGluingPullbackFlatQuotientFunctor R C D M).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (dgNerve R (DGGluingPullbackObject R C D M)) _⦋0⦌,
        Nonempty (VertexIso ((dgNerve.map (dgGluingPullbackInclusion R C D M)).app
          (Opposite.op ⦋0⦌) a) b) :=
  (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M) b).trans
      (dgGluingPullback_thickEssentialImage_iff R C D M hC hD b)
lemma dgGluingPullbackFlatQuotient_isLocalization :
    IsLocalization (dgGluingPullbackFlatQuotientFunctor R C D M)
      (cofiberLocalizingEdges
        {b | ∃ a : (dgNerve R (DGGluingPullbackObject R C D M)) _⦋0⦌,
          Nonempty (VertexIso ((dgNerve.map (dgGluingPullbackInclusion R C D M)).app
            (Opposite.op ⦋0⦌) a) b)}) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  have he :
      {b | ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R (DGGluingObject R C D M)
          (dgGluingPullbackProperty R C D M))) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R (DGGluingObject R C D M)
            (dgGluingPullbackProperty R C D M))).app (Opposite.op ⦋0⦌) a) b)} =
      {b | ∃ a : (dgNerve R (DGGluingPullbackObject R C D M)) _⦋0⦌,
        Nonempty (VertexIso ((dgNerve.map (dgGluingPullbackInclusion R C D M)).app
          (Opposite.op ⦋0⦌) a) b)} :=
    Set.ext (dgGluingPullback_thickEssentialImage_iff R C D M hC hD)
  have h := resolvedDGQuotientFunctor_isThickLocalization R (DGGluingObject R C D M)
    (dgGluingPullbackProperty R C D M)
  rw [he] at h
  exact h
end SerrePositivity.InfinityCategories
