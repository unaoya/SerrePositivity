module

public import SerrePositivity.BhattScholze.Andre.PowerRootPolynomialFractionBasis
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# André E1・E2：無限 p 冪根多項式環内のモニック商の自由性

## 概要

無限 p 冪根多項式環内で通常多項式 f の像を零とする商は、f がモニックなら
元の係数環上自由であり、正次数なら忠実平坦でもある。
BS Rem 7.15（著者版 p.62）の P/(fᵖ) の自由性の計算。

## 方針

通常多項式環上の小数指数基底を、通常モニック商へ基底変更する。
商とテンソルの標準同型を使い、通常モニック剰余の冪基底と合成する。

## 規約

係数環の標数・非零性は要求しない。自由性には正次数は不要。
prismatic envelope の Frobenius 引戻しとの同定は含まない。

## 使われ方

fᵖ に適用して、原典の具体的 pd 包の係数環の自由性と忠実平坦性を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open Polynomial
variable (R : Type u) [CommRing R] (p : ℕ) (hp : 0 < p)
local notation "P" => PowerRootPolynomial R p hp
local notation "F" => PowerRootFraction p hp

/-- 概要：通常多項式環を経由する係数作用は元の係数環の作用と整合する。
方針：標準評価代数射が係数を保つことを使う。
規約：元の加法モノイド環の R 作用を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の商の自由性のスカラー塔。 -/
theorem powerRootPolynomialBase_isScalarTower :
    letI := powerRootPolynomialBaseAlgebra R p hp
    IsScalarTower R R[X] P := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact IsScalarTower.of_algebraMap_eq' (powerRootPolynomialBaseMap R p hp).comp_algebraMap.symm

/-- 概要：通常多項式 f の像を零とする無限 p 冪根多項式環の商。
方針：標準多項式係数射で拡張した主イデアルで割る。
規約：係数環 R の作用を商に誘導する。
使われ方：BS Rem 7.15（著者版 p.62）の P/(fᵖ)。 -/
abbrev PowerRootPolynomialQuotient (f : R[X]) :=
  letI := powerRootPolynomialBaseAlgebra R p hp
  P ⧸ (Ideal.span {f}).map (algebraMap R[X] P)

/-- 概要：商を定める拡張イデアルは f の標準評価像の主イデアル。
方針：イデアルの span の像の公式を使う。
規約：通常変数は Y₀ に送る。
使われ方：BS Rem 7.15（著者版 p.62）の原典のモニック関係との照合。 -/
theorem powerRootPolynomialQuotient_ideal (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    (Ideal.span {f}).map (algebraMap R[X] P) =
      Ideal.span {powerRootPolynomialBaseMap R p hp f} := by
  let := powerRootPolynomialBaseAlgebra R p hp
  rw [Ideal.map_span, Set.image_singleton]
  rfl

/-- 概要：通常モニック商を経由する作用は元の係数環上の商作用と整合する。
方針：係数 r の両方の像を実商代表元で比較し、標準評価射の係数保存を使う。
規約：f のモニック性はこの作用の整合性には不要。
使われ方：BS Rem 7.15（著者版 p.62）の二つの基底の合成。 -/
theorem powerRootPolynomialQuotient_isScalarTower (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    IsScalarTower R (R[X] ⧸ Ideal.span {f}) (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change Ideal.Quotient.mk _ (algebraMap R P r) =
    Ideal.Quotient.mk _ (powerRootPolynomialBaseMap R p hp (Polynomial.C r))
  exact congrArg (Ideal.Quotient.mk _) ((powerRootPolynomialBaseMap R p hp).commutes r).symm

/-- 概要：無限 p 冪根モニック商は、通常モニック商上で小数指数を基底に持つ。
方針：小数指数基底を商環へ基底変更し、実商とテンソルの標準同型で戻す。
規約：この商環上の基底自体には f のモニック性を必要としない。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数環上の自由基底。 -/
def powerRootPolynomialQuotientFractionBasis (f : R[X]) :
    letI := powerRootPolynomialBaseAlgebra R p hp
    Module.Basis F (R[X] ⧸ Ideal.span {f}) (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  exact ((powerRootPolynomialFractionBasis R p hp).baseChange (R[X] ⧸ Ideal.span {f})).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor P (Ideal.span {f})).symm.toLinearEquiv

/-- 概要：モニック商は小数指数と通常剰余の冪を組み合わせた基底を持つ。
方針：通常モニック商の冪基底と、小数指数の基底変更をスカラー塔で合成する。
規約：正次数や係数環の非零性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の P/(fᵖ) の自由基底。 -/
def powerRootPolynomialQuotientBasis (f : R[X]) (hf : f.Monic) :
    Module.Basis (Fin f.natDegree × F) R (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let := powerRootPolynomialBase_isScalarTower R p hp
  let := powerRootPolynomialQuotient_isScalarTower R p hp f
  let bR : Module.Basis (Fin f.natDegree) R (R[X] ⧸ Ideal.span {f}) :=
    AdjoinRoot.powerBasisAux' hf
  exact bR.smulTower (powerRootPolynomialQuotientFractionBasis R p hp f)

/-- 概要：無限 p 冪根多項式環のモニック商は元の係数環上自由。
方針：具体的なモニック商基底から自由性を得る。
規約：自由性には正次数を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）のモニック冪商。 -/
theorem powerRootPolynomialQuotient_free (f : R[X]) (hf : f.Monic) :
    Module.Free R (PowerRootPolynomialQuotient R p hp f) :=
  Module.Free.of_basis (powerRootPolynomialQuotientBasis R p hp f hf)

/-- 概要：正次数モニックの無限 p 冪根多項式商は元の係数環上忠実平坦。
方針：零係数環を分け、非零枝では非空の具体的基底から非零性と自由忠実平坦性を得る。
規約：モニック定数 1 を除外するため正次数を要求する。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包への係数拡大。 -/
theorem powerRootPolynomialQuotient_faithfullyFlat (f : R[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PowerRootPolynomialQuotient R p hp f) := by
  let := powerRootPolynomialQuotient_free R p hp f hf
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    let a0 : F := ⟨0, by norm_num⟩
    let : Nonempty (Fin f.natDegree × F) := ⟨(⟨0, hdeg⟩, a0)⟩
    let b := powerRootPolynomialQuotientBasis R p hp f hf
    let : Nontrivial (PowerRootPolynomialQuotient R p hp f) := b.repr.symm.injective.nontrivial
    infer_instance

/-- 概要：無限 p 冪根多項式環におけるモニック多項式の像は非零因子。
方針：通常多項式環上のモニック元の正則性を、小数指数基底による平坦性で移す。
規約：零係数環も許し、正次数は要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の正則元の pd 包の計算。 -/
theorem powerRootPolynomial_monic_regular (f : R[X]) (hf : f.Monic) :
    IsSMulRegular P (powerRootPolynomialBaseMap R p hp f) := by
  let := powerRootPolynomialBaseAlgebra R p hp
  let := powerRootPolynomial_free_over_polynomial R p hp
  have hr : IsSMulRegular R[X] f := hf.isRegular.left
  exact hr.of_flat (S := P)

/-- 概要：モニック f の p 乗を課した無限 p 冪根多項式商は係数環上自由。
方針：モニック性が冪で保たれることを一般のモニック商の基底に適用する。
規約：係数環の標数や f の正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の P/(fᵖ) の自由性。 -/
theorem powerRootPolynomialPowerQuotient_free (f : R[X]) (hf : f.Monic) :
    Module.Free R (PowerRootPolynomialQuotient R p hp (f ^ p)) :=
  powerRootPolynomialQuotient_free R p hp (f ^ p) (hf.pow p)

/-- 概要：正次数モニック f の p 乗商は元の係数環上忠実平坦。
方針：モニック性と正次数の冪に関する公式を一般商の忠実平坦性へ渡す。
規約：p の素数性・係数環の標数は不要で、p の正値性だけを使う。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包の係数環。 -/
theorem powerRootPolynomialPowerQuotient_faithfullyFlat (f : R[X]) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (PowerRootPolynomialQuotient R p hp (f ^ p)) := by
  apply powerRootPolynomialQuotient_faithfullyFlat R p hp (f ^ p) (hf.pow p)
  rw [hf.natDegree_pow]
  exact Nat.mul_pos hp hdeg

end SerrePositivity.BhattScholze.Andre
