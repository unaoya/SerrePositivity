module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalTransition
public import SerrePositivity.KST.DerivedBlowup.ExceptionalSemilinearExterior
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGIdentity

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の有限重なりの例外因子 dg 遷移の恒等律。
方針：環射の恒等等式と標準恒等制限比較を挿入し、総外積の恒等律を使う。
規約：同じ有限集合・同じ pivot の場合。
使われ方：例外因子の共通基底環上の係数図式の単位条件。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の恒等重なり環射に沿う制限を元の dg 模型へ戻す比較。
方針：環射等式による移送と標準恒等制限比較を合成する。
規約：KST Lemma 3.6。使われ方：指定恒等遷移の行先をそろえる。 -/
def finiteOverlapExceptionalIdentityComparison (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    DGFunctor (FiniteOverlapRing R i T)
      (DGRestriction (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
        (FiniteOverlapExceptionalKoszulObject R a i T))
      (FiniteOverlapExceptionalKoszulObject R a i T) :=
  EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
    (restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
      (FiniteOverlapExceptionalKoszulObject R a i T))
    (restrictionIdentityDGFunctor (FiniteOverlapRing R i T)
      (FiniteOverlapExceptionalKoszulObject R a i T))

set_option maxHeartbeats 1000000 in
-- 局所化環上の係数制限の Hom 成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の恒等制限比較は各 Hom の元を変えない。
方針：環射等式による比較の成分公式を使う。
規約：KST Lemma 3.6。使われ方：恒等遷移を総外積上で計算する。 -/
theorem finiteOverlapExceptionalIdentityComparison_apply (a : I → R) (i : I) (T : Finset I)
    (hi : i ∈ T) (v w : FiniteOverlapExceptionalKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T)
      (FiniteOverlapExceptionalKoszulObject R a i T) v w).X q) :
    (((finiteOverlapExceptionalIdentityComparison R a i T hi).map v w).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor (finiteOverlapChartMap_ringHom_refl R i T hi)
    (FiniteOverlapExceptionalKoszulObject R a i T)).map v w).f q) z = z
  exact restrictionRingHomTransportDGFunctor_exterior_apply _ _ v w q z

set_option maxHeartbeats 2000000 in
-- 係数制限と指定遷移の豊穣 Hom を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：同じ有限重なりへの例外因子 dg 遷移は標準比較後に恒等。
方針：総外積へ包含し、実際の環射の恒等律と半線形遷移の恒等律を使う。
規約：KST Lemma 3.6。使われ方：例外因子の有限重なり図式の単位条件。 -/
theorem finiteOverlapExceptionalDGTransition_id (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapExceptionalDGTransition R a i i (Finset.Subset.refl T) hi)
        (finiteOverlapExceptionalIdentityComparison R a i T hi) =
      DGFunctor.id (FiniteOverlapExceptionalKoszulObject R a i T) := by
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (finiteOverlapExceptionalDGTransition R a i i (Finset.Subset.refl T) hi)
      (finiteOverlapExceptionalIdentityComparison R a i T hi))
    (G := DGFunctor.id (FiniteOverlapExceptionalKoszulObject R a i T))
    (fun v => by
      change (restrictionRingHomTransportDGFunctor
        (finiteOverlapChartMap_ringHom_refl R i T hi)
        (FiniteOverlapExceptionalKoszulObject R a i T)).obj .point = v
      rw [restrictionRingHomTransportDGFunctor_obj]) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R i T)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i)) q
  change exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
          (finiteOverlapCoordinates R i T) i)) q
      ((((finiteOverlapExceptionalIdentityComparison R a i T hi).map _ _).f q)
        (((finiteOverlapExceptionalDGTransition R a i i
          (Finset.Subset.refl T) hi).map v w).f q z)) =
    exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R i T)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
          (finiteOverlapCoordinates R i T) i)) q z
  rw [finiteOverlapExceptionalIdentityComparison_apply,
    finiteOverlapExceptionalDGTransition_inclusion]
  change exceptionalSemilinearExteriorMap
    (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
    (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R i T) i i _ = _
  rw [finiteOverlapChartMap_ringHom_refl, exceptionalSemilinearExteriorMap_id]

end SerrePositivity.KST.DerivedBlowup
