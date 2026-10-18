module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGComposition
public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapDGIdentity

/-!
概要：KST §3.1 の全有限重なり dg 遷移の合成・恒等律の各次数の元の公式。
方針：既存 dg 関手の等式を Hom の元で評価し、標準比較が元を変えないことを使う。
規約：係数作用の違いは型で保持し、各次数の関数の像を比較する。
使われ方：共通基底環へ制限した dg 図式の関手性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I]

set_option maxHeartbeats 2000000 in
-- 三つの局所化環の Hom の係数作用と成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの二段の dg 遷移は各次数の元の像として直接遷移に一致する。
方針：dg 合成律を成分で評価し、標準制限比較を解消する。
規約：KST §3.1。使われ方：共通基底環上の遷移の合成則。 -/
theorem finiteOverlapDGTransition_comp_apply (a : I → R) (i k l : I) {T U V : Finset I}
    (h : T ⊆ U) (g : U ⊆ V) (hi : i ∈ T) (hk : k ∈ U)
    (v w : FiniteOverlapKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T) v w).X q) :
    (((finiteOverlapDGTransition R a k l g hk).map _ _).f q)
        ((((finiteOverlapDGTransition R a i k h hi).map v w).f q) z) =
      (((finiteOverlapDGTransition R a i l (h.trans g) hi).map v w).f q) z := by
  have hc := congrArg (fun F : DGFunctor (FiniteOverlapRing R i T)
      (FiniteOverlapKoszulObject R a i T)
      (DGRestriction (finiteOverlapChartMap R i l (h.trans g) hi).toRingHom
        (FiniteOverlapKoszulObject R a l V)) =>
      exteriorCochainInclusion (chartKoszulDifferential
        (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
        (finiteOverlapCoordinates R l V) l) q (((F.map v w).f q).hom z))
    (finiteOverlapDGTransition_comp R a i k l h g hi hk)
  change exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R l V) (a j))
      (finiteOverlapCoordinates R l V) l) q
    ((((finiteOverlapDGCompositionComparison R a i k l h g hi hk).map _ _).f q)
      ((((finiteOverlapDGTransition R a k l g hk).map _ _).f q)
        ((((finiteOverlapDGTransition R a i k h hi).map v w).f q) z))) = _ at hc
  rw [finiteOverlapDGCompositionComparison_apply] at hc
  exact exteriorCochainInclusion_injective _ q hc

set_option maxHeartbeats 2000000 in
-- 局所化環の恒等遷移と元の Hom の成分を照合するために必要。
set_option synthInstance.maxHeartbeats 100000 in
-- 局所化環の複体のモノイダル構造を照合するために必要。
/-- 概要：有限重なりの恒等 dg 遷移は各次数の元を変えない。
方針：dg 恒等律を成分で評価し、標準恒等制限比較を解消する。
規約：KST §3.1。使われ方：共通基底環上の遷移の恒等則。 -/
theorem finiteOverlapDGTransition_id_apply (a : I → R) (i : I) (T : Finset I) (hi : i ∈ T)
    (v w : FiniteOverlapKoszulObject R a i T) (q : ℤ)
    (z : (homObject (FiniteOverlapRing R i T) (FiniteOverlapKoszulObject R a i T) v w).X q) :
    (((finiteOverlapDGTransition R a i i (Finset.Subset.refl T) hi).map v w).f q) z = z := by
  have hc := congrArg (fun F : DGFunctor (FiniteOverlapRing R i T)
      (FiniteOverlapKoszulObject R a i T) (FiniteOverlapKoszulObject R a i T) =>
      exteriorCochainInclusion (chartKoszulDifferential
        (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
        (finiteOverlapCoordinates R i T) i) q (((F.map v w).f q).hom z))
    (finiteOverlapDGTransition_id R a i T hi)
  change exteriorCochainInclusion (chartKoszulDifferential
      (fun j => algebraMap R (FiniteOverlapRing R i T) (a j))
      (finiteOverlapCoordinates R i T) i) q
    ((((finiteOverlapDGIdentityComparison R a i T hi).map _ _).f q)
      ((((finiteOverlapDGTransition R a i i (Finset.Subset.refl T) hi).map v w).f q) z)) = _ at hc
  rw [finiteOverlapDGIdentityComparison_apply] at hc
  exact exteriorCochainInclusion_injective _ q hc

end SerrePositivity.KST.DerivedBlowup
