module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermQuotientModel
public import SerrePositivity.CommutativeAlgebra.Adic.Reduction
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import Mathlib.RingTheory.TensorProduct.Maps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDSmallModelComparison
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDTermQuotientModel
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.PDDeRham.PDDeRhamRow

/-!
# 完備分冪項の冪商の線形比較

## 概要
完備分冪項と未完備項の有限冪商を基底上の線形同型で比較する。

## 方針
環商の比較が完備化単位を保つことを使い、未完備項の代表元上でスカラー作用を照合する。

## 規約
商は基底上の加群商として読む。

## 使われ方
BS 著者版 Theorem 6.4 の完備底変換の有限冪商の計算。
-/

public noncomputable section

open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
attribute [local instance] principalAdicQuotientAlgebra

variable (p : ℕ) (k : Type u) [CommRing k] (r n : ℕ)
variable (hr : Function.Injective (fun x : k => (p : k) * x))

local notation "Raw" => pdRaw k r n
local notation "Term" => pdTerm p k r n
local notation "U" => principalCompletionRingCatUnit p (CommRingCat.of Raw)

/-- 未完備項から完備項への標準の k 代数射。 -/
def pdTermCompletionUnitAlg : Raw →ₐ[k] Term :=
  ⟨(U).hom, fun _ => rfl⟩

private def quotientLinear (e : ℕ) :
    (Term ⧸ Ideal.span {(p : Term) ^ e}) ≃ₗ[k]
      (Raw ⧸ Ideal.span {(p : Raw) ^ e}) :=
  { (pdTermQuotientEquiv p k r n hr e).toAddEquiv with
    map_smul' := fun a x => by
      let q := pdTermQuotientEquiv p k r n hr e
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (q x)
      have hx : x = Ideal.Quotient.mk _ (U y) := by
        apply q.injective
        rw [pdTermQuotientEquiv_unit]
        exact hy.symm
      rw [hx]
      let f := pdTermCompletionUnitAlg p k r n
      change q (a • Ideal.Quotient.mk _ (f y)) = a • q (Ideal.Quotient.mk _ (f y))
      have hT (z : Term) : Ideal.Quotient.mk (Ideal.span {(p : Term)^e}) (a • z) =
          a • Ideal.Quotient.mk _ z := rfl
      have hf : f (a • y) = a • f y := f.toLinearMap.map_smul a y
      calc
        _ = q (Ideal.Quotient.mk _ (f (a • y))) :=
          congrArg q ((hT (f y)).symm.trans (congrArg (Ideal.Quotient.mk _) hf.symm))
        _ = Ideal.Quotient.mk _ (a • y) := pdTermQuotientEquiv_unit p k r n hr e (a • y)
        _ = a • Ideal.Quotient.mk (Ideal.span {(p : Raw)^e}) y := rfl
        _ = _ := congrArg (fun z => a • z) (pdTermQuotientEquiv_unit p k r n hr e y).symm }

private def principalReductionLinear (a : k) (R : Type u) [CommRing R] [Algebra k R] :
    AdicReduction (Ideal.span {a}) R ≃ₗ[k] R ⧸ Ideal.span {algebraMap k R a} :=
  { (principalAdicReductionEquiv a R).toAddEquiv with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := (Submodule.mkQ_surjective (Ideal.span {a} • (⊤ : Submodule k R))) x
      rfl }

/-- 基底上の有限冪商として読んだ完備項と未完備項の同型。 -/
def pdTermReductionEquiv (e : ℕ) :
    AdicReduction (Ideal.span {(p : k)^e}) Term ≃ₗ[k]
      AdicReduction (Ideal.span {(p : k)^e}) Raw := by
  let a := principalReductionLinear k ((p : k)^e) Term
  let b := principalReductionLinear k ((p : k)^e) Raw
  have hT : algebraMap k Term ((p : k)^e) = (p : Term)^e := by rw [map_pow, map_natCast]
  have hR : algebraMap k Raw ((p : k)^e) = (p : Raw)^e := by rw [map_pow, map_natCast]
  let a' := a.trans ((Ideal.quotientEquivAlgOfEq k (congrArg Ideal.span
    (congrArg Set.singleton hT))).toLinearEquiv)
  let b' := b.trans ((Ideal.quotientEquivAlgOfEq k (congrArg Ideal.span
    (congrArg Set.singleton hR))).toLinearEquiv)
  exact a'.trans ((quotientLinear p k r n hr e).trans b'.symm)

/-- 有限冪商の線形同型は標準の完備化単位と可換。 -/
theorem pdTermReductionEquiv_unit (e : ℕ) (x : Raw) :
    pdTermReductionEquiv p k r n hr e
      (Submodule.Quotient.mk (pdTermCompletionUnitAlg p k r n x)) =
        Submodule.Quotient.mk x := by
  have hT : algebraMap k Term ((p : k)^e) = (p : Term)^e := by rw [map_pow, map_natCast]
  have hR : algebraMap k Raw ((p : k)^e) = (p : Raw)^e := by rw [map_pow, map_natCast]
  let qT := (principalReductionLinear k ((p : k)^e) Term).trans
    ((Ideal.quotientEquivAlgOfEq k (congrArg Ideal.span
      (congrArg Set.singleton hT))).toLinearEquiv)
  let qR := (principalReductionLinear k ((p : k)^e) Raw).trans
    ((Ideal.quotientEquivAlgOfEq k (congrArg Ideal.span
      (congrArg Set.singleton hR))).toLinearEquiv)
  apply qR.injective
  change qR (qR.symm ((quotientLinear p k r n hr e)
    (qT (Submodule.Quotient.mk (pdTermCompletionUnitAlg p k r n x))))) =
      qR (Submodule.Quotient.mk x)
  rw [LinearEquiv.apply_symm_apply]
  change pdTermQuotientEquiv p k r n hr e
    (Ideal.Quotient.mk _ (pdTermCompletionUnitAlg p k r n x)) =
    Ideal.Quotient.mk _ x
  exact pdTermQuotientEquiv_unit p k r n hr e x


end SerrePositivity.BhattScholze.Prismatic
