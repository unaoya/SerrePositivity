module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGCoherenceData
public import SerrePositivity.KST.DerivedBlowup.RestrictionRingHomTransport

/-!
概要：KST §3.1 の全有限重なりの実際の dg 遷移の合成律。
方針：係数制限の合成比較と環射の合成等式の移送を明示し、総外積で比較する。
規約：有限重なりの包含に沿う二経路の行先を標準比較でそろえる。
使われ方：全有限チャート dg 図式の合成整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：二段の有限重なり環制限を直接射による制限にまとめる dg 比較。
方針：係数制限の合成比較と環図式の合成等式による比較を合成する。
規約：KST §3.1。使われ方：有限重なり dg 遷移の合成律の行先。 -/
def finiteOverlapDGCompositionComparison (a : I → R) (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    DGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i k h hi).toRingHom
        (DGRestriction (finiteOverlapChartMap R k l g hk).toRingHom
          (FiniteOverlapKoszulObject R a l V)))
      (DGRestriction (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom
        (FiniteOverlapKoszulObject R a l V)) :=
  EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
    (restrictionCompositionDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
      (finiteOverlapChartMap R k l g hk).toRingHom (FiniteOverlapKoszulObject R a l V))
    (restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk)
      (FiniteOverlapKoszulObject R a l V))

set_option maxHeartbeats 2000000 in
-- 三つの局所化環の係数制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの制限合成比較は各 Hom の元を変えない。
方針：二つの標準制限比較の成分公式を使う。
規約：KST §3.1。使われ方：有限重なり dg 合成律の総外積での比較。 -/
theorem finiteOverlapDGCompositionComparison_apply (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (v w : FiniteOverlapKoszulObject R a l V) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R l V) (FiniteOverlapKoszulObject R a l V) v w).X q) :
    (((finiteOverlapDGCompositionComparison R a i k l h g hi hk).map v w).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor
    (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk)
    (FiniteOverlapKoszulObject R a l V)).map v w).f q) z = z
  exact restrictionRingHomTransportDGFunctor_exterior_apply _ _ v w q z

set_option maxHeartbeats 2000000 in
-- 三つの局所化環の dg 遷移と係数制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：全有限重なりの dg 遷移の二段の合成は直接遷移と一致する。
方針：標準制限比較後に総外積へ包含し、半線形遷移の合成式と環・単元の合成律を使う。
規約：KST §3.1。使われ方：有限 Čech のチャート dg 図式の合成律。 -/
theorem finiteOverlapDGTransition_comp (a : I → R) (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapDGTransition R a i k h hi)
        (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
          (finiteOverlapDGTransition R a k l g hk)))
      (finiteOverlapDGCompositionComparison R a i k l h g hi hk) =
      finiteOverlapDGTransition R a i l (h.trans g) hi := by
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapDGTransition R a i k h hi)
        (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
          (finiteOverlapDGTransition R a k l g hk)))
      (finiteOverlapDGCompositionComparison R a i k l h g hi hk))
    (G := finiteOverlapDGTransition R a i l (h.trans g) hi)
    (fun _ => restrictionRingHomTransportDGFunctor_obj _ _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (chartKoszulDifferential
    (fun j => algebraMap R (FiniteOverlapRing R l V) (a j)) (finiteOverlapCoordinates R l V) l) q
  change exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R l V) (a j)) (finiteOverlapCoordinates R l V) l) q
    ((((finiteOverlapDGCompositionComparison R a i k l h g hi hk).map _ _).f q)
      (((finiteOverlapDGTransition R a k l g hk).map _ _).f q
        (((finiteOverlapDGTransition R a i k h hi).map v w).f q z))) =
    exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R l V) (a j)) (finiteOverlapCoordinates R l V) l) q
      (((finiteOverlapDGTransition R a i l (h.trans g) hi).map v w).f q z)
  rw [finiteOverlapDGCompositionComparison_apply, finiteOverlapDGTransition_inclusion,
    finiteOverlapDGTransition_inclusion, finiteOverlapDGTransition_inclusion]
  have hc := chartSemilinearExterior_comp (finiteOverlapChartMap R i k h hi).toRingHom
    (finiteOverlapChartMap R k l g hk).toRingHom
    (finiteOverlapCoordinates R k U) (finiteOverlapCoordinates R l V) i k l
    (finiteOverlapUnit R k U i (h hi)) (finiteOverlapUnit R l V k (g hk))
    (finiteOverlapChartMap_coordinates R k l g hk) (finiteOverlapUnit_val R k U i (h hi))
    (finiteOverlapUnit_val R l V k (g hk))
    (exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i) q z)
  refine hc.trans ?_
  rw [finiteOverlapDGTransition_unit_comp]
  exact congrArg (fun f : FiniteOverlapRing R i T →+* FiniteOverlapRing R l V =>
    ExteriorAlgebra.map (koszulGeneratorMap l i (finiteOverlapCoordinates R l V)
      (finiteOverlapUnit R l V i (g (h hi))))
      (freeExteriorScalarMap f (exteriorCochainInclusion (chartKoszulDifferential
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i) q z)))
    (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk)

end SerrePositivity.KST.DerivedBlowup
