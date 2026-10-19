module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalComposition
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapExceptionalIdentity

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の有限重なりの例外因子 dg 遷移の成分公式。
方針：全次数の元を総外積へ包含し、半線形遷移の合成・恒等則を使う。
規約：標準制限比較は元を変えないので、共通基底環への制限にも使える形にする。
使われ方：例外因子の共通基底環上の dg 代数関手の法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 三つの局所化環の Hom の各次数を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の実際の有限重なり遷移の二段の像は直接像と一致する。
方針：総外積の半線形合成則と実際の環射の合成等式を使う。
規約：KST Lemma 3.6。使われ方：基底制限後の Hom 写像の合成律。 -/
theorem finiteOverlapExceptionalDGTransition_comp_apply (a : I → R) (i k l : I)
    {T U V : Finset I} (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (v w : FiniteOverlapExceptionalKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T)
      (FiniteOverlapExceptionalKoszulObject R a i T) v w).X q) :
    (((finiteOverlapExceptionalDGTransition R a k l g hk).map _ _).f q)
        ((((finiteOverlapExceptionalDGTransition R a i k h hi).map v w).f q) z) =
      (((finiteOverlapExceptionalDGTransition R a i l (h.trans g) hi).map v w).f q) z := by
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R l V)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
        (finiteOverlapCoordinates R l V) l)) q
  rw [finiteOverlapExceptionalDGTransition_inclusion,
    finiteOverlapExceptionalDGTransition_inclusion, finiteOverlapExceptionalDGTransition_inclusion]
  change exceptionalSemilinearExteriorMap (finiteOverlapChartMap R k l g hk).toRingHom
      (finiteOverlapCoordinates R k U) (finiteOverlapCoordinates R l V) k l
      (exceptionalSemilinearExteriorMap (finiteOverlapChartMap R i k h hi).toRingHom
        (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R k U) i k _) =
    exceptionalSemilinearExteriorMap (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom
      (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R l V) i l _
  rw [exceptionalSemilinearExteriorMap_comp, finiteOverlapChartMap_ringHom_comp]

set_option maxHeartbeats 1000000 in
-- 局所化環上の恒等遷移と Hom の各次数を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環上の複体のモノイダル構造を照合するために必要。
/-- 概要：例外因子の実際の恒等重なり遷移は Hom の元を保つ。
方針：総外積へ包含して環射と半線形遷移の恒等律を使う。
規約：KST Lemma 3.6。使われ方：共通基底環上の恒等則。 -/
theorem finiteOverlapExceptionalDGTransition_id_apply (a : I → R) (i : I) (T : Finset I)
    (hi : i ∈ T) (v w : FiniteOverlapExceptionalKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T)
      (FiniteOverlapExceptionalKoszulObject R a i T) v w).X q) :
    (((finiteOverlapExceptionalDGTransition R a i i (Finset.Subset.refl T) hi).map v w).f q) z =
      z := by
  apply exteriorCochainInclusion_injective
    (Finsupp.linearCombination (FiniteOverlapRing R i T)
      (exceptionalRelationValue (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i)) q
  rw [finiteOverlapExceptionalDGTransition_inclusion]
  change exceptionalSemilinearExteriorMap
    (finiteOverlapChartMap R i i (Finset.Subset.refl T) hi).toRingHom
    (finiteOverlapCoordinates R i T) (finiteOverlapCoordinates R i T) i i _ = _
  rw [finiteOverlapChartMap_ringHom_refl, exceptionalSemilinearExteriorMap_id]

end SerrePositivity.KST.DerivedBlowup
