module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernel
public import SerrePositivity.InfinityCategories.Stable.UniverseKernelImage
/-!
概要：平坦源に取った同じ thick 核を元の dg 圏への包含として零対象反映に接続する。
方針：既存の商屋根の実頂点同型で元の零性を平坦源へ運び、同じ対象ラベルで核を選ぶ。
規約：同じ増大・同じ商関手を使い、厳密な逆 dg 関手は作らない。
使われ方：D-16 の元の resolvedDGQuotientFunctor の kernel 欄、任意の追加 ULift 版。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma resolvedDGQuotientFunctor_flat_vertex_zero_iff (P : Set D)
    (x : DGCategoryCellResolution.Source R D) :
    IsZeroVertex ((resolvedDGQuotientFunctor R D P).app (Opposite.op ⦋0⦌)
      (Simplex.vertex ((DGCategoryCellResolution.augmentation R D).obj x))) ↔
      IsZeroVertex ((resolvedDGQuotientProjection R D P).app
        (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
  have e := FunctorIso.app (resolvedDGQuotientRoofIso R D P) (Simplex.vertex x)
  change VertexIso
    ((resolvedDGQuotientFunctor R D P).app _
      ((dgNerve.map (DGCategoryCellResolution.augmentation R D)).app _ (Simplex.vertex x)))
    ((resolvedDGQuotientProjection R D P).app _ (Simplex.vertex x)) at e
  rw [dgFunctorNerve_vertex] at e
  exact ⟨fun h => h.of_vertexIso e, fun h => h.of_vertexIso e.symm⟩

lemma resolvedDGQuotientFunctor_zero_iff_thickEssentialImage (P : Set D)
    (b : (dgNerve R D) _⦋0⦌) :
    IsZeroVertex ((resolvedDGQuotientFunctor R D P).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b) := by
  constructor
  · intro h
    let x : DGCategoryCellResolution.Source R D := ⟨b.obj 0⟩
    have hz : IsZeroVertex ((resolvedDGQuotientProjection R D P).app
        (Opposite.op ⦋0⦌) (Simplex.vertex x)) := by
      apply (resolvedDGQuotientFunctor_flat_vertex_zero_iff R D P x).mp
      change IsZeroVertex ((resolvedDGQuotientFunctor R D P).app _ (Simplex.vertex (b.obj 0)))
      rw [dgNerve_vertex_obj]
      exact h
    have hx := (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).mp hz
    refine ⟨Simplex.vertex (⟨x, hx⟩ : resolvedDGQuotientThickFlatKernel R D P), ?_⟩
    rw [dgFunctorNerve_vertex]
    change Nonempty (VertexIso (Simplex.vertex (b.obj 0)) b)
    rw [dgNerve_vertex_obj]
    exact ⟨Iso.refl _⟩
  · rintro ⟨a, ⟨e⟩⟩
    obtain ⟨x, rfl⟩ := Simplex.vertexEquiv.symm.surjective a
    change VertexIso ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)).app
      (Opposite.op ⦋0⦌) (Simplex.vertex x)) b at e
    rw [dgFunctorNerve_vertex] at e
    have hz := (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x.val).mpr x.property
    exact ((resolvedDGQuotientFunctor_flat_vertex_zero_iff R D P x.val).mpr hz).of_vertexIso
      (e.map (resolvedDGQuotientFunctor R D P))

lemma resolvedDGQuotientFunctor_ulift_zero_iff_thickEssentialImage (P : Set D)
    (b : ((SSet.uliftFunctor.{w}).obj (dgNerve R D)) _⦋0⦌) :
    IsZeroVertex (((SSet.uliftFunctor.{w}).map (resolvedDGQuotientFunctor R D P)).app
      (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{w}).obj
          (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (VertexIso
          (((SSet.uliftFunctor.{w}).map
            (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b) :=
  zeroKernel_ulift_iff_essentialImage
    (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))
    (resolvedDGQuotientFunctor R D P)
    (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R D P) b

lemma resolvedDGQuotientThickKernelInclusion_isFullyFaithful (P : Set D) :
    IsFullyFaithful (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)) := by
  unfold resolvedDGQuotientThickKernelInclusion
  rw [dgNerve.map_comp]
  exact (resolvedDGQuotientThickFlatKernelInclusion_isFullyFaithful R D P).comp
    (dgCellAugmentationNerve_isQCatEquivalence R D).isFullyFaithful

lemma resolvedDGQuotientThickKernelInclusion_isExactFunctor
    [IsDGPretriangulated R D] (P : Set D) :
    IsExactFunctor (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)) := by
  let := resolvedDGQuotientThickFlatKernelInclusion_isExactFunctor R D P
  let := isExactFunctor_of_isQCatEquivalence (dgCellAugmentationNerve_isQCatEquivalence R D)
  unfold resolvedDGQuotientThickKernelInclusion
  rw [dgNerve.map_comp]
  exact isExactFunctor_comp _ _

end SerrePositivity.InfinityCategories
