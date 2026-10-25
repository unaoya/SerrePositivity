module
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientThickLocalization
public import SerrePositivity.InfinityCategories.F1B.Localization.UniverseAscent
/-!
概要：実商の thick 核局所化を任意の追加宇宙へ無条件に持ち上げる。
方針：同じ商の局所化を IsLocalization.ulift で持ち上げ、既存の反転辺同定で飽和する。
規約：既存の明示入力版を変更せず、quasicategory・ModelCategory 仮定を追加しない。
使われ方：D-16 の追加宇宙の quotient 欄。
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

lemma resolvedDGQuotientFunctor_ulift_isThickLocalization (P : Set D) :
    IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientFunctor R D P))
      (cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (VertexIso
            (((SSet.uliftFunctor.{w}).map
              (dgNerve.map (resolvedDGQuotientThickKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges]
  exact (resolvedDGQuotientFunctor_isLocalization R D P).ulift.saturate

lemma resolvedDGQuotientProjection_ulift_isThickLocalization (P : Set D) :
    IsLocalization ((SSet.uliftFunctor.{w}).map (resolvedDGQuotientProjection R D P))
      (cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (dgNerve R (resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (VertexIso
            (((SSet.uliftFunctor.{w}).map
              (dgNerve.map (resolvedDGQuotientThickFlatKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges]
  let := dgCellResolutionSource_isDGPretriangulated R D
  exact (dgQuotientNerveProjection_isLocalization R _ _
    (resolvedDGQuotient_localKFlat R D P)).ulift.saturate


end SerrePositivity.InfinityCategories
