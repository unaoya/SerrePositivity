module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalTransition
public import SerrePositivity.KST.DerivedBlowup.ExceptionalSemilinearExterior
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapRestrictionComparison

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の実際の有限重なり環に沿う例外因子遷移の合成。
方針：標準の制限合成比較と環射の合成等式を挿入し、総外積の半線形合成則を使う。
規約：既存の有限重なり環射を使い、二段制限と直接制限を区別する。
使われ方：例外因子の共通基底環上の係数図式の関手性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体と係数制限のモノイダル構造を照合するために必要。
/-- 概要：二段の例外因子の係数制限を直接環射の制限へまとめる指定比較。
方針：任意 dg 圏用の既存有限重なり制限比較を適用する。
規約：KST Lemma 3.6。使われ方：例外因子 dg 遷移の合成の行先をそろえる。 -/
abbrev finiteOverlapExceptionalCompositionComparison (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :=
  finiteOverlapRestrictionCompositionComparison R i k l h g hi hk
    (FiniteOverlapExceptionalKoszulObject R a l V)

set_option maxHeartbeats 2000000 in
-- 三つの局所化環の係数制限の Hom 成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の制限合成比較は各 Hom の元を変えない。
方針：制限合成比較と環射等式による比較の成分公式を使う。
規約：KST Lemma 3.6。使われ方：dg 合成則を総外積の合成則へ帰着する。 -/
theorem finiteOverlapExceptionalCompositionComparison_apply (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (v w : FiniteOverlapExceptionalKoszulObject R a l V) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R l V)
      (FiniteOverlapExceptionalKoszulObject R a l V) v w).X q) :
    (((finiteOverlapExceptionalCompositionComparison R a i k l h g hi hk).map v w).f q) z = z := by
  change (((restrictionRingHomTransportDGFunctor
    (finiteOverlapChartMap_ringHom_comp R i k l h g hi hk)
    (FiniteOverlapExceptionalKoszulObject R a l V)).map v w).f q) z = z
  exact restrictionRingHomTransportDGFunctor_exterior_apply _ _ v w q z

set_option maxHeartbeats 4000000 in
-- 三つの局所化環の dg Hom と二段の係数制限を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：実際の有限重なりの例外因子 dg 遷移の二段の合成は直接遷移に一致する。
方針：標準制限比較後に総外積へ包含し、半線形合成則と環射の合成等式を使う。
規約：KST Lemma 3.6、共通表示を介する明示 Koszul 計算による再構成。
使われ方：例外因子の全有限重なりの係数図式の合成則。 -/
theorem finiteOverlapExceptionalDGTransition_comp (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U) :
    EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapExceptionalDGTransition R a i k h hi)
        (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
          (finiteOverlapExceptionalDGTransition R a k l g hk)))
      (finiteOverlapExceptionalCompositionComparison R a i k l h g hi hk) =
      finiteOverlapExceptionalDGTransition R a i l (h.trans g) hi := by
  refine EnrichedFunctor.ext (Complex (FiniteOverlapRing R i T))
    (F := EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
      (EnrichedFunctor.comp (Complex (FiniteOverlapRing R i T))
        (finiteOverlapExceptionalDGTransition R a i k h hi)
        (restrictDGFunctor (finiteOverlapChartMap R i k h hi).toRingHom
          (finiteOverlapExceptionalDGTransition R a k l g hk)))
      (finiteOverlapExceptionalCompositionComparison R a i k l h g hi hk))
    (G := finiteOverlapExceptionalDGTransition R a i l (h.trans g) hi)
    (fun _ => restrictionRingHomTransportDGFunctor_obj _ _ _) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R l V)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
        (finiteOverlapCoordinates R l V) l)) q
  change exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R l V)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
          (finiteOverlapCoordinates R l V) l)) q
      ((((finiteOverlapExceptionalCompositionComparison R a i k l h g hi hk).map _ _).f q)
        (((finiteOverlapExceptionalDGTransition R a k l g hk).map _ _).f q
          (((finiteOverlapExceptionalDGTransition R a i k h hi).map v w).f q z))) =
    exteriorCochainInclusion
      (Finsupp.linearCombination (FiniteOverlapRing R l V)
        (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
          (finiteOverlapCoordinates R l V) l)) q
      (((finiteOverlapExceptionalDGTransition R a i l (h.trans g) hi).map v w).f q z)
  rw [finiteOverlapExceptionalCompositionComparison_apply,
    finiteOverlapExceptionalDGTransition_inclusion, finiteOverlapExceptionalDGTransition_inclusion,
    finiteOverlapExceptionalDGTransition_inclusion]
  change exceptionalSemilinearExteriorMap (finiteOverlapChartMap R k l g hk).toRingHom
      (finiteOverlapCoordinates R k U) (finiteOverlapCoordinates R l V) k l
      (exceptionalSemilinearExteriorMap (finiteOverlapChartMap R i k h hi).toRingHom
        (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R k U) i k _) =
    exceptionalSemilinearExteriorMap (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom
      (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R l V) i l _
  rw [exceptionalSemilinearExteriorMap_comp, finiteOverlapChartMap_ringHom_comp]

end SerrePositivity.KST.DerivedBlowup
