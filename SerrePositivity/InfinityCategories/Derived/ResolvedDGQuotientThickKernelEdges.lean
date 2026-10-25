module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernelSource
public import SerrePositivity.InfinityCategories.Stable.UniverseKernelEdges
/-!
概要：同じ実平坦商が反転する辺は、新しい thick 核に cofiber を持つ辺と一致する。
方針：平坦源と元の源の零対象反映を、完全関手の核の一般辺判定へ渡す。
規約：旧 Verdier 辺との無条件等式は主張せず、局所化の飽和移行は別に行う。
使われ方：D-16 の Sp quotient 欄の反転飽和、任意の追加 ULift 宇宙版。
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
  [IsDGPretriangulated R D]

lemma resolvedDGQuotientProjection_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    cofiberLocalizingEdges
      {b | ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b)} = invertedEdges (resolvedDGQuotientProjection R D P) := by
  let := dgCellResolutionSource_isDGPretriangulated R D
  let := dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := resolvedDGQuotientNerve_isStable R D P
  let hq : IsExactFunctor (resolvedDGQuotientProjection R D P) :=
    dgQuotientNerveProjection_isExactFunctor R _ _ (resolvedDGQuotient_localKFlat R D P)
  exact cofiberLocalizingEdges_eq_invertedEdges_of_kernel (resolvedDGQuotientProjection R D P) _
    (resolvedDGQuotientProjection_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientFunctor_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    cofiberLocalizingEdges
      {b | ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (VertexIso
          ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b)} = invertedEdges (resolvedDGQuotientFunctor R D P) := by
  let := dgNerve_isStable_of_pretriangulated R D
  let := resolvedDGQuotientNerve_isStable R D P
  let := resolvedDGQuotientFunctor_isExactFunctor R D P
  exact cofiberLocalizingEdges_eq_invertedEdges_of_kernel (resolvedDGQuotientFunctor R D P) _
    (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    cofiberLocalizingEdges
      {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
          (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (VertexIso
          (((SSet.uliftFunctor.{w}).map
            (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b)} =
      invertedEdges ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientProjection R D P)) := by
  let := dgCellResolutionSource_isDGPretriangulated R D
  let := dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := resolvedDGQuotientNerve_isStable R D P
  let hq : IsExactFunctor (resolvedDGQuotientProjection R D P) :=
    dgQuotientNerveProjection_isExactFunctor R _ _ (resolvedDGQuotient_localKFlat R D P)
  exact cofiberLocalizingEdges_ulift_essentialImage_eq_invertedEdges
    (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P))
    (resolvedDGQuotientProjection R D P)
    (resolvedDGQuotientProjection_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    cofiberLocalizingEdges
      {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
          (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (VertexIso
          (((SSet.uliftFunctor.{w}).map
            (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b)} =
      invertedEdges ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientFunctor R D P)) := by
  let := dgNerve_isStable_of_pretriangulated R D
  let := resolvedDGQuotientNerve_isStable R D P
  let := resolvedDGQuotientFunctor_isExactFunctor R D P
  exact cofiberLocalizingEdges_ulift_essentialImage_eq_invertedEdges
    (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))
    (resolvedDGQuotientFunctor R D P)
    (resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R D P)

end SerrePositivity.InfinityCategories
