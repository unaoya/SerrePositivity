module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGTransition
public import SerrePositivity.KST.DerivedBlowup.RestrictionRingHomTransport
public import SerrePositivity.KST.DerivedBlowup.RestrictionIdentity

/-!
概要：KST §3.1 の全有限重なりの dg 遷移の恒等律。
方針：環射の恒等等式と恒等制限比較を明示し、総外積上で恒等基底変換を計算する。
規約：同じ有限集合・同じ pivot への遷移。
使われ方：有限 Čech チャート dg 図式の恒等整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

/-- 概要：同じ有限重なりへの環射は環準同型としても恒等。
方針：代数射の恒等律の環準同型成分を取る。
規約：KST §3.1。使われ方：恒等制限比較の行先の同定。 -/
theorem finiteOverlapChartMap_ringHom_refl (i : I) (T : Finset I) (hi : i ∈ T) :
    (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom =
      RingHom.id (FiniteOverlapRing R i T) :=
  congrArg (fun f => f.toRingHom) (finiteOverlapChartMap_refl R i T hi)

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：同じ有限重なりへの係数制限を元の dg 模型へ戻す比較。
方針：環射の恒等等式による移送と恒等制限の標準比較を合成する。
規約：KST §3.1。使われ方：有限重なり dg 遷移の恒等律の行先。 -/
def finiteOverlapDGIdentityComparison (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    DGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
        (FiniteOverlapKoszulObject R a i T)) (FiniteOverlapKoszulObject R a i T) :=
  EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
    (restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
      (FiniteOverlapKoszulObject R a i T))
    (restrictionIdentityDGFunctor (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T))

set_option maxHeartbeats 1000000 in
-- 局所化環の恒等制限と環射等式の移送を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの恒等制限比較は各 Hom の元を変えない。
方針：環射の等式移送と恒等制限の成分公式を使う。
規約：KST §3.1。使われ方：dg 恒等律の総外積での比較。 -/
theorem finiteOverlapDGIdentityComparison_apply (a : I → R) (i : I) (T : Finset I)
    (hi : i ∈ T) (v w : FiniteOverlapKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T) v w).X q) :
    (((finiteOverlapDGIdentityComparison R a i T hi).map v w).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
    (FiniteOverlapKoszulObject R a i T)).map v w).f q) z = z
  exact restrictionRingHomTransportDGFunctor_exterior_apply _ _ v w q z

set_option maxHeartbeats 2000000 in
-- 局所化環の dg 遷移と恒等制限の標準比較を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：同じ有限重なりへの dg 遷移は標準比較後に恒等関手となる。
方針：Hom を総外積へ包含し、恒等環射と恒等基底変換を計算する。
規約：KST §3.1。使われ方：有限重なり dg 図式の恒等律。 -/
theorem finiteOverlapDGTransition_id (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (finiteOverlapDGTransition R a i i (Finset.Subset.refl T) hi)
      (finiteOverlapDGIdentityComparison R a i T hi) =
      EnrichedFunctor.id (Complex (FiniteOverlapRing R i T))
        (FiniteOverlapKoszulObject R a i T) := by
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (finiteOverlapDGTransition R a i i (Finset.Subset.refl T) hi)
      (finiteOverlapDGIdentityComparison R a i T hi))
    (G := EnrichedFunctor.id (Complex (FiniteOverlapRing R i T))
      (FiniteOverlapKoszulObject R a i T))
    (fun v => by
      change (restrictionRingHomTransportDGFunctor
        (finiteOverlapChartMap_ringHom_refl R i T hi)
        (FiniteOverlapKoszulObject R a i T)).obj .point = v
      rw [restrictionRingHomTransportDGFunctor_obj]) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective (chartKoszulDifferential
    (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T) i) q
  change exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j)) (finiteOverlapCoordinates R i T) i) q
    ((((finiteOverlapDGIdentityComparison R a i T hi).map _ _).f q)
      (((finiteOverlapDGTransition R a i i (Finset.Subset.refl T) hi).map v w).f q z)) =
    exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i) q z
  rw [finiteOverlapDGIdentityComparison_apply, finiteOverlapDGTransition_inclusion,
    finiteOverlapUnit_self, koszulGeneratorMap_self, ExteriorAlgebra.map_id]
  change freeExteriorScalarMap (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
    (exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i) q z) = _
  rw [finiteOverlapChartMap_ringHom_refl, freeExteriorScalarMap_id]

end SerrePositivity.KST.DerivedBlowup
