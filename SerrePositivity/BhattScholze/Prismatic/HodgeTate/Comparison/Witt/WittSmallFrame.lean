module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.PolynomialCompletionResidue
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCechFrameHomotopy
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittAdicCompleteness
public import Mathlib.Algebra.MvPolynomial.Equiv
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Coefficients.BigPDModel

/-!
# Witt 係数の有限分冪枠と大きい枠の比較

## 概要
有限個の多項式変数を、完備多項式の全元で添字づけられた枠の変数へ送る。

## 方針
二つの枠の剰余環を同一視し、表示独立性を適用する。

## 規約
大きい枠への写像は各多項式変数の完備化単位を添字とする変数を使う。

## 使われ方
BS 著者版 Theorem 6.4 の結晶比較を有限枠で検査するための比較。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Simplicial

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

local notation "C" => (A ⧸ P.ideal)
local notation "W" => WittVector p C
local notation "I" => Ideal.span {(p : C)}
local notation "J" => wittPdIdeal p C

local instance : Algebra W C := (wZero p C).toAlgebra

private def wittModPrime : W →+* C ⧸ I := (Ideal.Quotient.mk I).comp (wZero p C)

private theorem wittModPrime_ker : RingHom.ker (wittModPrime P) = J := by
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

private def wittResidueEquiv : W ⧸ J ≃+* C ⧸ I :=
  (Ideal.quotEquivOfEq (wittModPrime_ker P).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp (WittVector.constantCoeff_surjective p)))

private theorem wittResidueEquiv_mk (x : W) :
    wittResidueEquiv P (Ideal.Quotient.mk J x) = wittModPrime P x := by
  unfold wittResidueEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  rfl

variable (hpC : Function.Injective (fun x : A ⧸ P.ideal => (p : A ⧸ P.ideal) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A ⧸ P.ideal))
variable (Q : Poly (A ⧸ P.ideal))

local notation "B" => MvPolynomial (Fin Q.n) (W ⧸ J)
local notation "γ" => wittPdStructure p C hpC hlocal
local notation "hp" => p_mem_wittPdIdeal p C

private def smallResidueEquiv : B ≃ₐ[W] bigResidue P Q := by
  let e := (MvPolynomial.mapEquiv (Fin Q.n) (wittResidueEquiv P)).trans
    (polynomialResidueEquiv P hpC Q)
  refine { __ := e, commutes' := fun x => ?_ }
  change polynomialResidueEquiv P hpC Q
    (MvPolynomial.map (wittResidueEquiv P).toRingHom (MvPolynomial.C (Ideal.Quotient.mk J x))) = _
  rw [MvPolynomial.map_C]
  have h := polynomialResidueEquiv_map P hpC Q (MvPolynomial.C (wZero p C x))
  rw [MvPolynomial.map_C] at h
  exact (congrArg (fun a => polynomialResidueEquiv P hpC Q (MvPolynomial.C a))
    (wittResidueEquiv_mk P x)).trans h

private theorem smallResidueEquiv_X (j : Fin Q.n) :
    smallResidueEquiv P hpC Q (MvPolynomial.X j) =
      Ideal.Quotient.mk _ (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j)) := by
  unfold smallResidueEquiv
  change polynomialResidueEquiv P hpC Q
    (MvPolynomial.map (wittResidueEquiv P).toRingHom (MvPolynomial.X j)) = _
  rw [MvPolynomial.map_X]
  have h := polynomialResidueEquiv_map P hpC Q (MvPolynomial.X j)
  rwa [MvPolynomial.map_X] at h

private theorem smallResidue_ker : J ≤ RingHom.ker (algebraMap W B) := by
  intro x hx
  change MvPolynomial.C (Ideal.Quotient.mk J x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

private theorem bigResidue_ker_witt : J ≤ RingHom.ker (algebraMap W (bigResidue P Q)) :=
  bigResidue_ker P (show J ≤ _ from le_rfl) Q

private def smallFrame : ULift.{u} (Fin Q.n) → B := fun j => MvPolynomial.X j.down

private def smallIndex (j : ULift.{u} (Fin Q.n)) : polyCompletion P Q.n :=
  prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j.down)

private def smallFrameOnBigResidue : ULift.{u} (Fin Q.n) → bigResidue P Q :=
  smallResidueEquiv P hpC Q ∘ smallFrame P Q

private def smallFrameChangeResidue :
    pdCechNerve p γ hp (smallResidue_ker P Q) (smallFrame P Q) ≅
      pdCechNerve p γ hp (bigResidue_ker_witt P Q) (smallFrameOnBigResidue P hpC Q) where
  hom := PDCechNerve.rename p γ hp (smallResidue_ker P Q) (bigResidue_ker_witt P Q)
    (smallFrame P Q) (smallFrameOnBigResidue P hpC Q) (smallResidueEquiv P hpC Q).toAlgHom id
      (fun _ => rfl)
  inv := PDCechNerve.rename p γ hp (bigResidue_ker_witt P Q) (smallResidue_ker P Q)
    (smallFrameOnBigResidue P hpC Q) (smallFrame P Q) (smallResidueEquiv P hpC Q).symm.toAlgHom id
      (fun x => ((smallResidueEquiv P hpC Q).symm_apply_apply (smallFrame P Q x)).symm)
  hom_inv_id := by
    rw [PDCechNerve.rename_comp]
    refine (PDCechNerve.rename_congr p γ hp _ _ _ _ _ _ _ ?_ rfl).trans
      (PDCechNerve.rename_id ..)
    apply AlgHom.ext
    intro x
    exact (smallResidueEquiv P hpC Q).symm_apply_apply x
  inv_hom_id := by
    rw [PDCechNerve.rename_comp]
    refine (PDCechNerve.rename_congr p γ hp _ _ _ _ _ _ _ ?_ rfl).trans
      (PDCechNerve.rename_id ..)
    apply AlgHom.ext
    intro x
    exact (smallResidueEquiv P hpC Q).apply_symm_apply x

private def largeFrame : polyCompletion P Q.n → bigResidue P Q := Ideal.Quotient.mk _

private def frameLift (j : ULift.{u} (Fin Q.n)) :
    ((pdCechNerve p γ hp (bigResidue_ker_witt P Q) (largeFrame P Q)).obj ⦋0⦌).right :=
  PDCechNerve.variableImage p γ hp (bigResidue_ker_witt P Q) (largeFrame P Q) 0
    (smallIndex P Q j, 0)

private theorem frameLift_spec (j : ULift.{u} (Fin Q.n)) :
    pdCechAugmentation p γ hp (bigResidue_ker_witt P Q) (largeFrame P Q)
      (frameLift P hpC hlocal Q j) = smallFrameOnBigResidue P hpC Q j := by
  change PDCechNerve.augmentation p γ hp (bigResidue_ker_witt P Q) (largeFrame P Q) 0
    (frameLift P hpC hlocal Q j) = _
  unfold frameLift
  rw [PDCechNerve.augmentation_variableImage]
  exact (smallResidueEquiv_X P hpC Q j.down).symm

private def frameMap :
    pdCechNerve p γ hp (bigResidue_ker_witt P Q) (smallFrameOnBigResidue P hpC Q) ⟶
      pdCechNerve p γ hp (bigResidue_ker_witt P Q) (largeFrame P Q) :=
  pdCechNerveMap p γ hp (bigResidue_ker_witt P Q) (smallFrameOnBigResidue P hpC Q)
    (largeFrame P Q) (frameLift P hpC hlocal Q) (frameLift_spec P hpC hlocal Q)

private theorem smallFrameEval_surjective :
    Function.Surjective (pdFrameEval (k := W) (smallFrame P Q) 0) := by
  have h : (pdFrameEval (k := W) (smallFrame P Q) 0).toRingHom =
      (MvPolynomial.map (Ideal.Quotient.mk J)).comp
        (MvPolynomial.rename (fun x : ULift.{u} (Fin Q.n) × Fin 1 => x.1.down)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (pdFrameEval (k := W) (smallFrame P Q) 0) (MvPolynomial.C a) = _
      change (pdFrameEval (k := W) (smallFrame P Q) 0) (MvPolynomial.C a) =
        MvPolynomial.map (Ideal.Quotient.mk J)
          (MvPolynomial.rename (fun x : ULift.{u} (Fin Q.n) × Fin 1 => x.1.down)
            (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, MvPolynomial.map_C]
      exact (pdFrameEval (k := W) (smallFrame P Q) 0).commutes a
    · intro x
      change (pdFrameEval (k := W) (smallFrame P Q) 0) (MvPolynomial.X x) =
        MvPolynomial.map (Ideal.Quotient.mk J)
          (MvPolynomial.rename (fun x : ULift.{u} (Fin Q.n) × Fin 1 => x.1.down)
            (MvPolynomial.X x))
      rw [pdFrameEval_X, MvPolynomial.rename_X, MvPolynomial.map_X]
      rfl
  change Function.Surjective (pdFrameEval (k := W) (smallFrame P Q) 0).toRingHom
  rw [h]
  exact (MvPolynomial.map_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).comp
    (MvPolynomial.rename_surjective _ (fun j => ⟨(⟨j⟩, 0), rfl⟩))

private theorem smallFrameOnBigResidue_surjective :
    Function.Surjective (pdFrameEval (k := W) (smallFrameOnBigResidue P hpC Q) 0) := by
  have h : pdFrameEval (k := W) (smallFrameOnBigResidue P hpC Q) 0 =
      (smallResidueEquiv P hpC Q).toAlgHom.comp (pdFrameEval (k := W) (smallFrame P Q) 0) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [pdFrameEval_X, AlgHom.comp_apply, pdFrameEval_X]
    rfl
  rw [h]
  exact (smallResidueEquiv P hpC Q).surjective.comp (smallFrameEval_surjective P Q)

private theorem largeFrameEval_surjective :
    Function.Surjective (pdFrameEval (k := W) (largeFrame P Q) 0) := by
  intro a
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨MvPolynomial.X (x, 0), pdFrameEval_X (largeFrame P Q) 0 _⟩

variable (hk : IsAdicComplete (Ideal.span {(p : A ⧸ P.ideal)}) (A ⧸ P.ideal))

include hpC hk in
private theorem wittComplete : IsAdicComplete (Ideal.span {(p : W)}) W :=
  @witt_isAdicComplete p _ C _ hk hpC

private def smallIso :
    pdModel p W Q.n ≅ pdCechNerve p γ hp (smallResidue_ker P Q) (smallFrame P Q) :=
  pdModel_iso_pdCechNerve p W γ hp
    (fun _ => (γ).factorial_mul_dpow_eq_pow hp) (wittComplete P hpC hk)
      (witt_mul_prime_injective p C hpC) Q.n (smallResidue_ker P Q)

/-- Witt 係数の有限分冪模型から大きい枠への比較。 -/
def wittSmallFrame : pdModel p W Q.n ⟶ (wittBigPdModel P hpC hlocal).obj Q := by
  unfold wittBigPdModel bigPDModel
  exact (smallIso P hpC hlocal Q hk).hom ≫ (smallFrameChangeResidue P hpC hlocal Q).hom ≫
    frameMap P hpC hlocal Q

/-- 有限枠から大きい枠への比較は交代余面複体で擬同型。 -/
theorem wittSmallFrame_quasiIso :
    QuasiIso ((AlgebraicTopology.alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (wittSmallFrame P hpC hlocal Q hk) (PDCechNerve.algebraModule W))) := by
  let F := (Functor.whiskeringRight SimplexCategory _ _).obj (PDCechNerve.algebraModule W) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _
  have h : QuasiIso (F.map (frameMap P hpC hlocal Q)) :=
    pdCechNerveMap_quasiIso p γ hp (bigResidue_ker_witt P Q) (smallFrameOnBigResidue P hpC Q)
      (largeFrame P Q) (frameLift P hpC hlocal Q) (frameLift_spec P hpC hlocal Q)
      (wittComplete P hpC hk) (smallFrameOnBigResidue_surjective P hpC Q)
      (largeFrameEval_surjective P Q)
  change QuasiIso (F.map (wittSmallFrame P hpC hlocal Q hk))
  change QuasiIso (F.map ((smallIso P hpC hlocal Q hk).hom ≫
    (smallFrameChangeResidue P hpC hlocal Q).hom ≫ frameMap P hpC hlocal Q))
  rw [F.map_comp, F.map_comp]
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
