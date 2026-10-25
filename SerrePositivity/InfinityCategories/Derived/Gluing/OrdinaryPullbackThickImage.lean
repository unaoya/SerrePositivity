module
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackThickFlatTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.OrdinaryPullbackFlatQuotient
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickLocalization
/-!
概要：実平坦 thick 核の本質像は元の通常 pullback 包含の本質像と一致する。
方針：増大で対象条件を戻し、逆向きには同じ対象ラベルの平坦対象を選ぶ。
規約：同じ元包含・同じ商関手を保持する。
使われ方：D-16 の核反映と局所化を元の通常 pullback へ移す。
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
lemma dgGluingPullback_thickEssentialImage_iff (b : (dgNerve R (DGGluingObject R C D M)) _⦋0⦌) :
    (∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R (DGGluingObject R C D M)
        (dgGluingPullbackProperty R C D M))) _⦋0⦌,
      Nonempty (VertexIso
        ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R (DGGluingObject R C D M)
          (dgGluingPullbackProperty R C D M))).app (Opposite.op ⦋0⦌) a) b)) ↔
    ∃ a : (dgNerve R (DGGluingPullbackObject R C D M)) _⦋0⦌,
      Nonempty (VertexIso ((dgNerve.map (dgGluingPullbackInclusion R C D M)).app
        (Opposite.op ⦋0⦌) a) b) := by
  let := dgGluing_isDGPretriangulated R C D M hC hD
  let := dgCellResolutionSource_isDGPretriangulated R (DGGluingObject R C D M)
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    let y : DGGluingPullbackObject R C D M :=
      ⟨(DGCategoryCellResolution.augmentation R (DGGluingObject R C D M)).obj x.val,
        dgGluingPullbackProperty_of_flatThick R C D M hC hD x.val x.property⟩
    refine ⟨Simplex.vertex y, ?_⟩
    erw [dgFunctorNerve_vertex] at e ⊢
    exact ⟨e⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨y, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    let x : DGCategoryCellResolution.Source R (DGGluingObject R C D M) := ⟨y.val⟩
    have hx : dgThickClosureProperty R _
        (resolvedDGNullObjects R (DGGluingObject R C D M)
          (dgGluingPullbackProperty R C D M)) x := by
      apply (dgThickClosureProperty_iff_nativeStableRetract R _ _ x).mpr
      exact ⟨x, StableVertexClosure.of_mem ⟨x, y.property, rfl⟩, ⟨Retract.refl _⟩⟩
    refine ⟨Simplex.vertex (⟨x, hx⟩ : resolvedDGQuotientThickFlatKernel R
      (DGGluingObject R C D M) (dgGluingPullbackProperty R C D M)), ?_⟩
    erw [dgFunctorNerve_vertex] at e ⊢
    exact ⟨e⟩
end SerrePositivity.InfinityCategories
