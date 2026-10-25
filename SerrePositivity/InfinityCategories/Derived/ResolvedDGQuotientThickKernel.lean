module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientThickKernelCriterion
public import SerrePositivity.InfinityCategories.Derived.DGFullKernelStability
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientFlatKernel
public import SerrePositivity.InfinityCategories.Stable.ExactFunctorKernelEdges
/-!
概要：同じ実平坦商の核を、tria の retract 閉包から新しい小 dg 核として構成する。
方針：既存の平坦分解と商を保持し、実零頂点の反映を新核の本質像へ接続する。
規約：旧安定閉包・指定零化集合・Verdier 辺は変更せず、新名だけを追加する。
使われ方：D-16 の Sp 向け kernel 欄と商の反転飽和の同定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGQuotient DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

abbrev resolvedDGQuotientThickFlatKernel (P : Set D) :=
  DGFullSubcategory (DGCategoryCellResolution.Source R D)
    (dgThickClosureProperty R (DGCategoryCellResolution.Source R D)
      (resolvedDGNullObjects R D P))

lemma resolvedDGQuotientThickFlatKernel_small (P : Set D) :
    Small.{u} (resolvedDGQuotientThickFlatKernel R D P) := inferInstance

def resolvedDGQuotientThickFlatKernelInclusion (P : Set D) :
    DGFunctor R (resolvedDGQuotientThickFlatKernel R D P)
      (DGCategoryCellResolution.Source R D) :=
  dgFullSubcategoryInclusion R _ _

def resolvedDGQuotientThickKernelInclusion (P : Set D) :
    DGFunctor R (resolvedDGQuotientThickFlatKernel R D P) D :=
  (resolvedDGQuotientThickFlatKernelInclusion R D P).comp
    (DGCategoryCellResolution.augmentation R D)

lemma resolvedDGQuotientProjection_vertex_isZero_iff_thick (P : Set D)
    (x : DGCategoryCellResolution.Source R D) :
    IsZeroVertex ((resolvedDGQuotientProjection R D P).app
      (Opposite.op ⦋0⦌) (Simplex.vertex x)) ↔
      dgThickClosureProperty R (DGCategoryCellResolution.Source R D)
        (resolvedDGNullObjects R D P) x := by
  change IsZeroVertex ((dgNerve.map (inclusion R (DGCategoryCellResolution.Source R D)
    (resolvedDGNullObjects R D P))).app (Opposite.op ⦋0⦌) (Simplex.vertex x)) ↔ _
  rw [dgFunctorNerve_vertex]
  exact dgQuotient_vertex_isZero_iff_thick R _ _ (resolvedDGQuotient_localKFlat R D P) x

lemma resolvedDGQuotientProjection_zero_iff_thickEssentialImage (P : Set D)
    (b : (dgNerve R (DGCategoryCellResolution.Source R D)) _⦋0⦌) :
    IsZeroVertex ((resolvedDGQuotientProjection R D P).app (Opposite.op ⦋0⦌) b) ↔
      ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b) :=
  dgFullKernel_zero_iff_essentialImage R _ _ (resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm) b

lemma resolvedDGQuotientProjection_ulift_zero_iff_thickEssentialImage (P : Set D)
    (b : ((SSet.uliftFunctor.{w}).obj
      (dgNerve R (DGCategoryCellResolution.Source R D))) _⦋0⦌) :
    IsZeroVertex (((SSet.uliftFunctor.{w}).map (resolvedDGQuotientProjection R D P)).app
      (Opposite.op ⦋0⦌) b) ↔
      ∃ a : ((SSet.uliftFunctor.{w}).obj
          (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (VertexIso
          (((SSet.uliftFunctor.{w}).map
            (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b) :=
  dgFullKernel_ulift_zero_iff_essentialImage R _ _ (resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm) b

lemma resolvedDGQuotientThickFlatKernel_isStable [IsDGPretriangulated R D] (P : Set D) :
    IsStable (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) := by
  let := dgCellResolutionSource_isDGPretriangulated R D
  let := dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := resolvedDGQuotientNerve_isStable R D P
  let hq : IsExactFunctor (resolvedDGQuotientProjection R D P) :=
    dgQuotientNerveProjection_isExactFunctor R _ _ (resolvedDGQuotient_localKFlat R D P)
  exact dgFullKernelNerve_isStable R _ _ (resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm)

lemma resolvedDGQuotientThickFlatKernelInclusion_isExactFunctor
    [IsDGPretriangulated R D] (P : Set D) :
    IsExactFunctor (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P)) := by
  let := dgCellResolutionSource_isDGPretriangulated R D
  let := dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := resolvedDGQuotientNerve_isStable R D P
  let hq : IsExactFunctor (resolvedDGQuotientProjection R D P) :=
    dgQuotientNerveProjection_isExactFunctor R _ _ (resolvedDGQuotient_localKFlat R D P)
  exact dgFullKernelInclusion_isExactFunctor R _ _ (resolvedDGQuotientProjection R D P)
    (fun x => (resolvedDGQuotientProjection_vertex_isZero_iff_thick R D P x).symm)

lemma resolvedDGQuotientThickFlatKernelInclusion_isFullyFaithful (P : Set D) :
    IsFullyFaithful (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P)) :=
  dgFullSubcategoryInclusionNerve_isFullyFaithful R _ _

end SerrePositivity.InfinityCategories
