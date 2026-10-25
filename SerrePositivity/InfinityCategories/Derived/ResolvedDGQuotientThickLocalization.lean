module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickKernelEdges
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientLocalization
public import SerrePositivity.InfinityCategories.F1B.Localization.Saturation
/-!
概要：同じ実商の局所化を、新しい thick 核に cofiber を持つ辺の局所化へ移す。
方針：Ind が公開した反転飽和への一般補題と、新しい辺集合の同定を使う。
規約：既存の Verdier 辺・商関手を保持し、持ち上げた局所化そのものは明示入力に分ける。
使われ方：D-16 の Sp quotient 欄。追加宇宙での残る一般供給境界も型で明示する。
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

lemma resolvedDGQuotientProjection_isThickLocalization (P : Set D) :
    IsLocalization (resolvedDGQuotientProjection R D P)
      (cofiberLocalizingEdges
        {b | ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
          Nonempty (VertexIso
            ((dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P)).app
              (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientProjection_thickCofiberEdges_eq_invertedEdges]
  let := dgCellResolutionSource_isDGPretriangulated R D
  exact (dgQuotientNerveProjection_isLocalization R _ _
    (resolvedDGQuotient_localKFlat R D P)).saturate

lemma resolvedDGQuotientFunctor_isThickLocalization (P : Set D) :
    IsLocalization (resolvedDGQuotientFunctor R D P)
      (cofiberLocalizingEdges
        {b | ∃ a : (dgNerve R (resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
          Nonempty (VertexIso
            ((dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P)).app
              (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientFunctor_thickCofiberEdges_eq_invertedEdges]
  exact (resolvedDGQuotientFunctor_isLocalization R D P).saturate

lemma resolvedDGQuotientFunctor_ulift_isThickLocalization_of_isLocalization (P : Set D)
    (W : Set (((SSet.uliftFunctor.{w}).obj (dgNerve R D)) _⦋1⦌))
    (hq : IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientFunctor R D P)) W) :
    IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientFunctor R D P))
      (cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (VertexIso
            (((SSet.uliftFunctor.{w}).map
              (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges]
  exact hq.saturate

lemma resolvedDGQuotientProjection_ulift_isThickLocalization_of_isLocalization (P : Set D)
    (W : Set (((SSet.uliftFunctor.{w}).obj
      (dgNerve R (DGCategoryCellResolution.Source R D))) _⦋1⦌))
    (hq : IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientProjection R D P)) W) :
    IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientProjection R D P))
      (cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (VertexIso
            (((SSet.uliftFunctor.{w}).map
              (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges]
  exact hq.saturate

end SerrePositivity.InfinityCategories
