module
public import SerrePositivity.CommutativeAlgebra.Polynomial.MonicRelation

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Logic.Equiv.Option
public import Mathlib.RingTheory.Regular.IsSMulRegular
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialExpand
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import SerrePositivity.BhattScholze.Perfectoidization.WittPushout
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import SerrePositivity.CommutativeAlgebra.CompletelyFlat.Basic
public import SerrePositivity.HomologicalAlgebra.Tor

/-!
# 通常のモニック根の添加と冪根の添加（BS 著者版 Theorem 7.14 の証明の R̃ の有限版）

## 概要
独立変数ごとのモニック関係式 fᵢ(Xᵢ) と係数商での正則性、通常のモニック根添加 R[X]/(f) の自由性、任意元族の冪根添加環 R[X_s]/(X_sⁿ − c_s) の普遍性・商表示・自由性・完全忠実平坦性。

## 方針
δ 構造を使わない可換環論として述べる。独立モニック関係の正則列（`CommutativeAlgebra/KoszulRegular/MonicRelation`）は KST が import しているので別ファイルのまま残す。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/JetRegularity`、`Envelope/MonicCandidate`、`Envelope/Normalized`、`Envelope/RootRelation`、`OrdinaryRoots/Family`、`PowerRootEnvelope/DividedPowerPrime`、`PowerRootEnvelope/Varpi`、`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u v w

/-! ## André：独立変数のモニック関係式

## 概要

任意のモニック多項式を多変数多項式環の指定変数で評価すると非零因子になる。
BS 著者版 Remark 7.15(1)（p.62）の pd 包の計算に必要な正則性の通常代数部分である。

## 方針

指定変数を一変数多項式として分離し、係数変更されたモニック多項式の正則性を移送する。
既存の冪根関係式の場合と同じ証明を任意のモニック多項式へ一般化する。

## 規約

係数環は任意で零環も許す。この正則性だけには正次数は不要である。
pd 包との比較や完備化後の忠実平坦性は主張しない。

## 使われ方

一元のモニック関係式と、独立変数の有限族を扱う際の最初の正則性入力に使う。
-/

@[expose] public noncomputable section MonicPowerFamilyCover

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] polynomialExpandAlgebra
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 根添加のテンソル積で用いるexpand作用の加群構造を明示する。 -/
abbrev monicPowerFamilyExpandModule :
    Module (MvPolynomial σ R) (PolynomialExpandTarget n σ R) :=
  @Algebra.toModule (MvPolynomial σ R) (PolynomialExpandTarget n σ R)
    inferInstance inferInstance (polynomialExpandAlgebra n σ R)

attribute [local instance] monicPowerFamilyExpandModule

/-- X_s^n=c_sを課した通常の根添加環を、既存テンソル積の基底変更で実現する。 -/
def MonicPowerFamilyCover (c : σ → R) :=
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  @TensorProduct (MvPolynomial σ R) inferInstance R (PolynomialExpandTarget n σ R)
    inferInstance inferInstance inferInstance (monicPowerFamilyExpandModule n σ R)

instance monicPowerFamilyCoverCommRing (c : σ → R) : CommRing (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change CommRing (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

instance monicPowerFamilyCoverAlgebra (c : σ → R) : Algebra R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change Algebra R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 元c_sの指定したn乗根。 -/
def monicPowerFamilyRoot (c : σ → R) (s : σ) : MonicPowerFamilyCover n σ R c := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  exact TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
    (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))

/-- 指定した根は実際にc_sの像をn乗根として持つ。 -/
theorem monicPowerFamilyRoot_pow (c : σ → R) (s : σ) :
    monicPowerFamilyRoot n σ R c s ^ n = algebraMap R (MonicPowerFamilyCover n σ R c) (c s) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change (TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
      (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))) ^ n =
    c s ⊗ₜ[MvPolynomial σ R] (1 : PolynomialExpandTarget n σ R)
  rw [Algebra.TensorProduct.tmul_pow, one_pow]
  have h := TensorProduct.smul_tmul (R := MvPolynomial σ R)
    (MvPolynomial.X s : MvPolynomial σ R) (1 : R) (1 : PolynomialExpandTarget n σ R)
  have hL : (MvPolynomial.X s : MvPolynomial σ R) • (1 : R) = c s := by
    change MvPolynomial.aeval c (MvPolynomial.X s) * 1 = c s
    rw [MvPolynomial.aeval_X, mul_one]
  have hR : (MvPolynomial.X s : MvPolynomial σ R) • (1 : PolynomialExpandTarget n σ R) =
      (ULift.up (MvPolynomial.X s) : PolynomialExpandTarget n σ R) ^ n := by
    change ULift.up (MvPolynomial.expand n (MvPolynomial.X s)) * 1 =
      (ULift.up (MvPolynomial.X s) : PolynomialExpandTarget n σ R) ^ n
    rw [mul_one, MvPolynomial.expand_X]
    rfl
  rw [hL, hR] at h
  exact h.symm

/-- n>0なら通常の根添加環は係数環上自由。任意個の元を同時に扱う。 -/
theorem monicPowerFamilyCover_moduleFree (c : σ → R) (hn : 0 < n) :
    Module.Free R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let := polynomialExpand_moduleFree n σ R hn
  change Module.Free R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 通常の根添加環は平坦。有限性・Noether性は不要。 -/
theorem monicPowerFamilyCover_moduleFlat (c : σ → R) (hn : 0 < n) :
    Module.Flat R (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFree n σ R c hn
  infer_instance

/-- 非零係数環では通常の根添加環は忠実平坦。 -/
theorem monicPowerFamilyCover_moduleFaithfullyFlat [Nontrivial R] (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MonicPowerFamilyCover n σ R c) := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let := polynomialExpand_moduleFaithfullyFlat n σ R hn
  change Module.FaithfullyFlat R (R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R)
  infer_instance

/-- 零係数環も含む、通常根添加環の忠実平坦性。 -/
theorem monicPowerFamilyCover_moduleFaithfullyFlat_all (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MonicPowerFamilyCover n σ R c) := by
  rcases subsingleton_or_nontrivial R with hs | hnR
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨monicPowerFamilyCover_moduleFlat n σ R c hn, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hnR
    exact monicPowerFamilyCover_moduleFaithfullyFlat n σ R c hn

end SerrePositivity.BhattScholze

end MonicPowerFamilyCover

/-! ## 通常のモニック冪根添加環の普遍性

指定した冪根を持つ任意の通常環への、係数と根を保つ一意な写像を構成する。
完備性・perfectoid性は要求しない。
-/

@[expose] public noncomputable section MonicPowerFamilyUniversal

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
attribute [local instance] polynomialExpandAlgebra monicPowerFamilyExpandModule
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- expand作用の型名と台多項式環の標準ULift同型。 -/
def monicPowerFamilyTargetEquiv : PolynomialExpandTarget n σ R ≃+* MvPolynomial σ R :=
  ULift.ringEquiv

/-- テンソル積の右因子から根添加環への標準射。 -/
def monicPowerFamilyCoverRightMap (c : σ → R) :
    PolynomialExpandTarget n σ R →+* MonicPowerFamilyCover n σ R c := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  exact (Algebra.TensorProduct.includeRight : PolynomialExpandTarget n σ R →ₐ[MvPolynomial σ R]
    R ⊗[MvPolynomial σ R] PolynomialExpandTarget n σ R).toRingHom

/-- 右因子の係数は、根添加環の標準係数射の像と一致する。 -/
theorem monicPowerFamilyCoverRightMap_C (c : σ → R) (r : R) :
    monicPowerFamilyCoverRightMap n σ R c (ULift.up (MvPolynomial.C r)) =
      algebraMap R (MonicPowerFamilyCover n σ R c) r := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let P := MvPolynomial σ R
  let Q := R ⊗[P] PolynomialExpandTarget n σ R
  have hb : algebraMap P (PolynomialExpandTarget n σ R) (MvPolynomial.C r) =
      ULift.up (MvPolynomial.C r) := by
    change ULift.up (MvPolynomial.expand n (MvPolynomial.C r)) = _
    rw [MvPolynomial.expand_C]
  have ha : algebraMap P R (MvPolynomial.C r) = r := MvPolynomial.aeval_C c r
  have hright := (Algebra.TensorProduct.includeRight :
    PolynomialExpandTarget n σ R →ₐ[P] Q).commutes (MvPolynomial.C r)
  have hleft := (Algebra.TensorProduct.includeLeft : R →ₐ[P] Q).commutes (MvPolynomial.C r)
  rw [hb] at hright
  rw [ha] at hleft
  exact hright.trans hleft.symm

/-- 右因子の変数の像は、指定した根。 -/
@[simp] theorem monicPowerFamilyCoverRightMap_X (c : σ → R) (s : σ) :
    monicPowerFamilyCoverRightMap n σ R c (ULift.up (MvPolynomial.X s)) =
      monicPowerFamilyRoot n σ R c s := rfl

/-- 根添加環からの環射は、係数と指定根の像で決まる。 -/
theorem monicPowerFamilyCoverHom_ext (c : σ → R) {U : Type w} [CommRing U]
    (L M : MonicPowerFamilyCover n σ R c →+* U)
    (hR : L.comp (algebraMap R (MonicPowerFamilyCover n σ R c)) =
      M.comp (algebraMap R (MonicPowerFamilyCover n σ R c)))
    (hroot : ∀ s, L (monicPowerFamilyRoot n σ R c s) = M (monicPowerFamilyRoot n σ R c s)) :
    L = M := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  apply Algebra.TensorProduct.ringHom_ext
  · exact hR
  · let i := monicPowerFamilyCoverRightMap n σ R c
    let e := monicPowerFamilyTargetEquiv n σ R
    have he : (L.comp i).comp e.symm.toRingHom = (M.comp i).comp e.symm.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r
        change L (i (ULift.up (MvPolynomial.C r))) = M (i (ULift.up (MvPolynomial.C r)))
        rw [monicPowerFamilyCoverRightMap_C]
        exact RingHom.congr_fun hR r
      · intro s
        exact hroot s
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun he (e x)
    change L (i (e.symm (e x))) = M (i (e.symm (e x))) at hx
    rw [e.symm_apply_apply] at hx
    exact hx

/-- 指定根を持つ終域への環射を、既存テンソル積の普遍射から構成する。 -/
def monicPowerFamilyCoverMap (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    MonicPowerFamilyCover n σ R c →+* U := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  let e := monicPowerFamilyTargetEquiv n σ R
  let g := (MvPolynomial.eval₂Hom f b).comp e.toRingHom
  have he : f.comp (algebraMap (MvPolynomial σ R) R) =
      g.comp (algebraMap (MvPolynomial σ R) (PolynomialExpandTarget n σ R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f (MvPolynomial.aeval c (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom f b (MvPolynomial.expand n (MvPolynomial.C r))
      rw [MvPolynomial.aeval_C, MvPolynomial.expand_C, MvPolynomial.eval₂Hom_C]
      rfl
    · intro s
      change f (MvPolynomial.aeval c (MvPolynomial.X s)) =
        MvPolynomial.eval₂Hom f b (MvPolynomial.expand n (MvPolynomial.X s))
      rw [MvPolynomial.aeval_X, MvPolynomial.expand_X, map_pow, MvPolynomial.eval₂Hom_X']
      exact (hb s).symm
  exact _root_.SerrePositivity.coefficientTensorLift f g (RingHom.congr_fun he)

/-- 普遍射は係数射を保つ。 -/
theorem monicPowerFamilyCoverMap_comp (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    (monicPowerFamilyCoverMap n σ R c f b hb).comp
      (algebraMap R (MonicPowerFamilyCover n σ R c)) = f := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  apply RingHom.ext
  intro r
  change monicPowerFamilyCoverMap n σ R c f b hb
    (r ⊗ₜ[MvPolynomial σ R] (1 : PolynomialExpandTarget n σ R)) = f r
  change f r * ((MvPolynomial.eval₂Hom f b).comp
    (monicPowerFamilyTargetEquiv n σ R).toRingHom) 1 = f r
  rw [map_one, mul_one]

/-- 普遍射は指定根を保つ。 -/
@[simp] theorem monicPowerFamilyCoverMap_root (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) (s : σ) :
    monicPowerFamilyCoverMap n σ R c f b hb (monicPowerFamilyRoot n σ R c s) = b s := by
  let : Algebra (MvPolynomial σ R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  change monicPowerFamilyCoverMap n σ R c f b hb
    (TensorProduct.tmul (R := MvPolynomial σ R) (M := R)
      (N := PolynomialExpandTarget n σ R) 1 (ULift.up (MvPolynomial.X s))) = b s
  change f 1 * MvPolynomial.eval₂Hom f b (MvPolynomial.X s) = b s
  rw [map_one, one_mul, MvPolynomial.eval₂Hom_X']

/-- 任意の通常環の指定n乗根への、係数と根を保つ環射は一意に存在する。 -/
theorem existsUnique_monicPowerFamilyCoverMap (c : σ → R) {U : Type w} [CommRing U]
    (f : R →+* U) (b : σ → U) (hb : ∀ s, b s ^ n = f (c s)) :
    ∃! L : MonicPowerFamilyCover n σ R c →+* U,
      L.comp (algebraMap R (MonicPowerFamilyCover n σ R c)) = f ∧
        ∀ s, L (monicPowerFamilyRoot n σ R c s) = b s := by
  refine ⟨monicPowerFamilyCoverMap n σ R c f b hb,
    ⟨monicPowerFamilyCoverMap_comp n σ R c f b hb,
      monicPowerFamilyCoverMap_root n σ R c f b hb⟩, ?_⟩
  intro L hL
  exact monicPowerFamilyCoverHom_ext n σ R c L _
    (hL.1.trans (monicPowerFamilyCoverMap_comp n σ R c f b hb).symm)
    (fun s ↦ (hL.2 s).trans (monicPowerFamilyCoverMap_root n σ R c f b hb s).symm)

end SerrePositivity.BhattScholze

end MonicPowerFamilyUniversal

/-! ## 通常冪根添加環の商表示

通常のテンソル積による構成を、実際のモニック関係式による商へ結び付ける。
完備化やperfectoid性の比較はここでは主張しない。
-/

@[expose] public noncomputable section MonicPowerFamilyPresentation

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- 指定した冪根の関係式のイデアル。 -/
def monicPowerFamilyRelationIdeal (c : σ → R) : Ideal (MvPolynomial σ R) :=
  Ideal.span (Set.range fun s => MvPolynomial.X s ^ n - MvPolynomial.C (c s))

/-- 係数と指定根による多項式の評価。 -/
def monicPowerFamilyEvaluation (c : σ → R) :
    MvPolynomial σ R →+* MonicPowerFamilyCover n σ R c :=
  (MvPolynomial.aeval (monicPowerFamilyRoot n σ R c)).toRingHom

/-- 評価は実際の関係式イデアルを消す。 -/
theorem monicPowerFamilyEvaluation_kills (c : σ → R) :
    ∀ a ∈ monicPowerFamilyRelationIdeal n σ R c,
      monicPowerFamilyEvaluation n σ R c a = 0 := by
  have h : monicPowerFamilyRelationIdeal n σ R c ≤
      RingHom.ker (monicPowerFamilyEvaluation n σ R c) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨s, rfl⟩
    change monicPowerFamilyEvaluation n σ R c
      (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) = 0
    simp [monicPowerFamilyEvaluation, monicPowerFamilyRoot_pow]
  exact fun a ha => h ha

/-- 関係式の商から通常根添加環への具体的な写像。 -/
def monicPowerFamilyQuotientMap (c : σ → R) :
    MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c →+*
      MonicPowerFamilyCover n σ R c :=
  Ideal.Quotient.lift _ (monicPowerFamilyEvaluation n σ R c)
    (monicPowerFamilyEvaluation_kills n σ R c)

/-- 商の標準変数は指定した冪根の関係式を満たす。 -/
theorem monicPowerFamilyQuotient_root_pow (c : σ → R) (s : σ) :
    (Ideal.Quotient.mk (monicPowerFamilyRelationIdeal n σ R c) (MvPolynomial.X s)) ^ n =
      algebraMap R (MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c) (c s) := by
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.subset_span (Set.mem_range_self s) :
      MvPolynomial.X s ^ n - MvPolynomial.C (c s) ∈
        monicPowerFamilyRelationIdeal n σ R c)
  rw [map_sub, map_pow, sub_eq_zero] at h
  exact h

/-- 指定根の普遍射による逆向きの写像。 -/
def monicPowerFamilyCoverToQuotient (c : σ → R) :
    MonicPowerFamilyCover n σ R c →+*
      MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c :=
  monicPowerFamilyCoverMap n σ R c (algebraMap R _)
    (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
    (monicPowerFamilyQuotient_root_pow n σ R c)

/-- 商からの写像と普遍射の合成は、根添加環上の恒等射。 -/
theorem monicPowerFamilyQuotientMap_comp_coverToQuotient (c : σ → R) :
    (monicPowerFamilyQuotientMap n σ R c).comp
      (monicPowerFamilyCoverToQuotient n σ R c) = RingHom.id _ := by
  apply monicPowerFamilyCoverHom_ext
  · ext r
    have h := RingHom.congr_fun (monicPowerFamilyCoverMap_comp n σ R c
      (algebraMap R _) (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
      (monicPowerFamilyQuotient_root_pow n σ R c)) r
    change monicPowerFamilyQuotientMap n σ R c
      (monicPowerFamilyCoverToQuotient n σ R c (algebraMap R _ r)) = _
    rw [show monicPowerFamilyCoverToQuotient n σ R c (algebraMap R _ r) =
      algebraMap R _ r from h]
    change monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) = _
    simp [monicPowerFamilyEvaluation]
  · intro s
    change monicPowerFamilyQuotientMap n σ R c
      (monicPowerFamilyCoverToQuotient n σ R c (monicPowerFamilyRoot n σ R c s)) = _
    rw [show monicPowerFamilyCoverToQuotient n σ R c (monicPowerFamilyRoot n σ R c s) =
      Ideal.Quotient.mk _ (MvPolynomial.X s) from monicPowerFamilyCoverMap_root ..]
    change monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) = _
    simp [monicPowerFamilyEvaluation]

/-- 逆の合成も実際の関係式商上の恒等射。 -/
theorem monicPowerFamilyCoverToQuotient_comp_quotientMap (c : σ → R) :
    (monicPowerFamilyCoverToQuotient n σ R c).comp
      (monicPowerFamilyQuotientMap n σ R c) = RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change monicPowerFamilyCoverToQuotient n σ R c
      (monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r)) = _
    rw [show monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) =
      algebraMap R _ r by simp [monicPowerFamilyEvaluation]]
    exact RingHom.congr_fun (monicPowerFamilyCoverMap_comp n σ R c
      (algebraMap R _) (fun s => Ideal.Quotient.mk _ (MvPolynomial.X s))
      (monicPowerFamilyQuotient_root_pow n σ R c)) r
  · intro s
    change monicPowerFamilyCoverToQuotient n σ R c
      (monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s)) = _
    rw [show monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) =
      monicPowerFamilyRoot n σ R c s by simp [monicPowerFamilyEvaluation]]
    exact monicPowerFamilyCoverMap_root ..

/-- 通常冪根添加環は、モニック関係式による商と同型。 -/
def monicPowerFamilyPresentationEquiv (c : σ → R) :
    MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c ≃+*
      MonicPowerFamilyCover n σ R c :=
  RingEquiv.ofRingHom (monicPowerFamilyQuotientMap n σ R c)
    (monicPowerFamilyCoverToQuotient n σ R c)
    (monicPowerFamilyQuotientMap_comp_coverToQuotient n σ R c)
    (monicPowerFamilyCoverToQuotient_comp_quotientMap n σ R c)

/-- 商表示同型は標準係数射と両立する。 -/
@[simp] theorem monicPowerFamilyPresentationEquiv_coeff (c : σ → R) (r : R) :
    monicPowerFamilyPresentationEquiv n σ R c (algebraMap R _ r) =
      algebraMap R (MonicPowerFamilyCover n σ R c) r := by
  change monicPowerFamilyEvaluation n σ R c (MvPolynomial.C r) = _
  simp [monicPowerFamilyEvaluation]

/-- 商表示同型は変数の剰余を指定した根へ送る。 -/
@[simp] theorem monicPowerFamilyPresentationEquiv_root (c : σ → R) (s : σ) :
    monicPowerFamilyPresentationEquiv n σ R c
      (Ideal.Quotient.mk _ (MvPolynomial.X s)) = monicPowerFamilyRoot n σ R c s := by
  change monicPowerFamilyEvaluation n σ R c (MvPolynomial.X s) = _
  simp [monicPowerFamilyEvaluation]

/-- 標準R代数構造についてのモニック商表示同型。 -/
def monicPowerFamilyPresentationAlgEquiv (c : σ → R) :
    (MvPolynomial σ R ⧸ monicPowerFamilyRelationIdeal n σ R c) ≃ₐ[R]
      MonicPowerFamilyCover n σ R c :=
  AlgEquiv.ofRingEquiv (monicPowerFamilyPresentationEquiv_coeff n σ R c)

end SerrePositivity.BhattScholze

end MonicPowerFamilyPresentation

/-! ## モニック冪根添加の係数商との比較

既存の係数商・二重商・モニック商表示の同型を合成する。
BSの有限δ剰余の表示へ適用するための比較。
-/

@[expose] public noncomputable section MonicPowerFamilyBaseQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable (n : ℕ) (σ : Type u) (R : Type v) [CommRing R]

/-- モニック関係式は係数の商と既存係数商同型で、剰余係数の関係式へ移る。 -/
theorem monicPowerFamilyRelationIdeal_map_coefficientQuotient (I : Ideal R) (c : σ → R) :
    ((monicPowerFamilyRelationIdeal n σ R c).map
      (Ideal.Quotient.mk (I.map (MvPolynomial.C : R →+* MvPolynomial σ R)))).map
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingHom =
      monicPowerFamilyRelationIdeal n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)) := by
  rw [Ideal.map_map, monicPowerFamilyCoefficientQuotient_comp]
  simp only [monicPowerFamilyRelationIdeal, Ideal.map_span, ← Set.range_comp', map_sub, map_pow,
    MvPolynomial.map_X, MvPolynomial.map_C]

/-- 係数イデアルとモニック冪関係式による商は、係数商上の通常根添加環。 -/
def monicPowerFamilyBaseQuotientEquiv (I : Ideal R) (c : σ → R) :
    (MvPolynomial σ R ⧸ (I.map (MvPolynomial.C : R →+* MvPolynomial σ R) ⊔
      monicPowerFamilyRelationIdeal n σ R c)) ≃+*
      MonicPowerFamilyCover n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)) :=
  ((DoubleQuot.quotQuotEquivQuotSup
    (I.map (MvPolynomial.C : R →+* MvPolynomial σ R))
    (monicPowerFamilyRelationIdeal n σ R c)).symm.trans
    (Ideal.quotientEquiv _ _
      (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm.toRingEquiv
      (monicPowerFamilyRelationIdeal_map_coefficientQuotient n σ R I c).symm)).trans
    (monicPowerFamilyPresentationEquiv n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s)))

/-- 係数商比較同型は標準商射上で既存モニック商射と一致する。 -/
theorem monicPowerFamilyBaseQuotientEquiv_mk (I : Ideal R) (c : σ → R)
    (x : MvPolynomial σ R) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c
      (Ideal.Quotient.mk (I.map MvPolynomial.C ⊔ monicPowerFamilyRelationIdeal n σ R c) x) =
      monicPowerFamilyQuotientMap n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s))
        (Ideal.Quotient.mk _ (MvPolynomial.map (Ideal.Quotient.mk I) x)) := by
  change monicPowerFamilyQuotientMap n σ (R ⧸ I) (fun s => Ideal.Quotient.mk I (c s))
    (Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp (Ideal.Quotient.mk I)) MvPolynomial.X x)) = _
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]

/-- 係数商比較同型は元の係数を標準係数射の像へ送る。 -/
@[simp] theorem monicPowerFamilyBaseQuotientEquiv_C (I : Ideal R) (c : σ → R) (r : R) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c
      (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      algebraMap (R ⧸ I) (MonicPowerFamilyCover n σ (R ⧸ I)
        (fun s => Ideal.Quotient.mk I (c s))) (Ideal.Quotient.mk I r) := by
  rw [monicPowerFamilyBaseQuotientEquiv_mk, MvPolynomial.map_C]
  change monicPowerFamilyEvaluation n σ (R ⧸ I) _ (MvPolynomial.C _) = _
  simp [monicPowerFamilyEvaluation]

/-- 係数商比較同型は変数を指定根へ送る。 -/
@[simp] theorem monicPowerFamilyBaseQuotientEquiv_X (I : Ideal R) (c : σ → R) (s : σ) :
    monicPowerFamilyBaseQuotientEquiv n σ R I c (Ideal.Quotient.mk _ (MvPolynomial.X s)) =
      monicPowerFamilyRoot n σ (R ⧸ I) (fun t => Ideal.Quotient.mk I (c t)) s := by
  rw [monicPowerFamilyBaseQuotientEquiv_mk, MvPolynomial.map_X]
  change monicPowerFamilyEvaluation n σ (R ⧸ I) _ (MvPolynomial.X s) = _
  simp [monicPowerFamilyEvaluation]

end SerrePositivity.BhattScholze

end MonicPowerFamilyBaseQuotient

/-! ## André：係数商後のモニック関係の正則性

## 概要

任意の係数イデアルで割った後も、指定変数のモニック関係式は非零因子である。
BS 著者版 Corollary 2.39（p.25）、BS 著者版 Remark 7.15(1)（p.62）の正則性入力を供給する。

## 方針

係数商と多項式環の交換同型で元の商を移し、モニック性の係数変更と変数分離を使う。
既存の冪根族のファイルから使うのは任意多項式上の係数射の恒等式だけである。

## 規約

係数環・係数イデアルは任意で、正次数や δ 構造を要求しない。
実導来還元の離散性や prismatic envelope の比較は別工程である。

## 使われ方

任意モニック f を入力する一元 raw δ p 除算の p 正則性の前提に用いる。
-/

@[expose] public noncomputable section MonicRelationResidue

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

/-- 概要：モニック関係式の評価は係数変更と可換である。
方針：多項式評価の環射に関する自然性を使う。
規約：モニック性自体はこの恒等式には不要である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の残余関係式を同定する。 -/
theorem monicRelation_map {R : Type u} {B : Type w} [CommRing R] [CommRing B]
    {σ : Type v} (φ : R →+* B) (f : Polynomial R) (s : σ) :
    MvPolynomial.map φ (monicRelation f s) = monicRelation (f.map φ) s := by
  unfold monicRelation
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, MvPolynomial.map_X]
  congr 1
  ext a
  simp

/-- 概要：係数商に沿う拡張イデアルで割っても、モニック関係式の像は非零因子。
方針：多変数多項式環と係数商の交換同型を通じて既知の正則性へ帰着する。
規約：零環と任意イデアルを許す。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の mod p 正則性をモニック性から供給する。 -/
theorem monicRelation_coefficientQuotient_isSMulRegular
    {R : Type u} [CommRing R] {σ : Type v}
    (I : Ideal R) (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R ⧸ I.map MvPolynomial.C)
      (Ideal.Quotient.mk (I.map MvPolynomial.C) (monicRelation f s)) := by
  let e := (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I).symm
  have he : e (Ideal.Quotient.mk (I.map MvPolynomial.C) (monicRelation f s)) =
      monicRelation (f.map (Ideal.Quotient.mk I)) s := by
    rw [← monicRelation_map]
    exact DFunLike.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ R I) _
  have h := monicRelation_isSMulRegular (f.map (Ideal.Quotient.mk I))
    (hf.map (Ideal.Quotient.mk I)) s
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

/-- 概要：モニック関係式は実際の p 主イデアル商でも非零因子。
方針：係数の p 主イデアルの多項式環への像を照合する。
規約：p の素数性・係数環の p 正則性は不要。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の raw δ 除算の正則性入力。 -/
theorem monicRelation_modP_isSMulRegular
    {R : Type u} [CommRing R] {σ : Type v}
    (p : ℕ) (f : Polynomial R) (hf : f.Monic) (s : σ) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span {(p : MvPolynomial σ R)})
      (Ideal.Quotient.mk (Ideal.span {(p : MvPolynomial σ R)}) (monicRelation f s)) := by
  have h := monicRelation_coefficientQuotient_isSMulRegular (Ideal.span {(p : R)}) f hf s
  have hI : (Ideal.span {(p : R)}).map (MvPolynomial.C : R →+* MvPolynomial σ R) =
      Ideal.span {(p : MvPolynomial σ R)} := by
    rw [Ideal.map_span]
    simp only [Set.image_singleton, map_natCast]
  rw [hI] at h
  exact h

end SerrePositivity.BhattScholze.Andre

end MonicRelationResidue

/-! ## André：通常のモニック根添加の自由性

## 概要

正次数のモニック多項式の通常根添加環は自由かつ忠実平坦である。
有限段の変数置換 `Y = Z^n` と関係式の冪にも同じ結論を与える。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15(1)（p.62）の通常代数の準備である。

## 方針

Mathlib のモニック剰余の冪基底を使う。非零係数環では正次数から係数射の単射性を得て、
自由加群の忠実平坦性を適用する。零係数環は加群の自明性で処理する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の準備で、pd 包との同定は含まない。

## 規約

正次数を明示する。`1` はモニックだが根添加環が零となり、非零の係数環上忠実平坦でない。
自由性だけから perfectoid 性や完備化後の忠実平坦性を推論しない。

## 使われ方

`R/ϖ[Y^(1/p^∞)]/(f^p)` の有限段に必要なモニック商の計算に使う。
-/

@[expose] public noncomputable section OrdinaryMonicRoot

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open Polynomial

/-- 概要：正次数モニックの根添加環は係数環上忠実平坦。
方針：モニック剰余の自由性と係数射の単射性を使い、零環は別に処理する。
規約：次数の仮定は定数 `1` を除外する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）のモニック商の有限段の準備。 -/
theorem adjoinRoot_faithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R (AdjoinRoot f) := by
  let := hf.free_adjoinRoot
  rcases subsingleton_or_nontrivial R with hs | hn
  · let := hs
    rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
    refine ⟨inferInstance, ?_⟩
    intro N _ _ _
    exact Module.subsingleton R N
  · let := hn
    let : Nontrivial (AdjoinRoot f) :=
      (AdjoinRoot.of.injective_of_monic_of_degree_pos hf
        (natDegree_pos_iff_degree_pos.mp hdeg)).nontrivial
    infer_instance

/-- 概要：正次数モニックに根を添加した通常の自由忠実平坦拡大が存在する。
方針：`AdjoinRoot f` とその標準根を取る。
規約：完備性・perfectoid 性は結論に含まない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の一段の通常代数部分。 -/
theorem exists_monicRootedFaithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (r : T),
      (letI := φ.toAlgebra; Module.Free R T ∧ Module.FaithfullyFlat R T) ∧
      f.eval₂ φ r = 0 := by
  refine ⟨AdjoinRoot f, inferInstance, algebraMap R (AdjoinRoot f),
    AdjoinRoot.root f, ?_, ?_⟩
  · rw [toAlgebra_algebraMap]
    exact ⟨hf.free_adjoinRoot, adjoinRoot_faithfullyFlat f hf hdeg⟩
  · exact AdjoinRoot.eval₂_root f

/-- 概要：モニック f の変数を n 乗に置換した後の m 乗関係式も、自由忠実平坦な商を与える。
方針：expand と冪のモニック性・次数公式を通常根添加の結果に適用する。
規約：`n,m` は正であり、有限段の商だけを扱う。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の `P/(f^p)` の有限段。 -/
theorem expandedPower_quotient_free_faithfullyFlat {R : Type u} [CommRing R]
    (f : R[X]) (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Module.Free R (AdjoinRoot ((expand R n f) ^ m)) ∧
      Module.FaithfullyFlat R (AdjoinRoot ((expand R n f) ^ m)) := by
  have he : (expand R n f).Monic := hf.expand hn
  have hd : 0 < ((expand R n f) ^ m).natDegree := by
    rw [he.natDegree_pow, natDegree_expand]
    exact Nat.mul_pos hm (Nat.mul_pos hdeg hn)
  exact ⟨(he.pow m).free_adjoinRoot,
    adjoinRoot_faithfullyFlat _ (he.pow m) hd⟩

end SerrePositivity.BhattScholze.Andre

end OrdinaryMonicRoot

/-! ## 非零指数の通常冪根関係の正則性

任意の係数環で、指定した変数のモニック冪関係式は非零因子となる。
δ構造や指数の素数性は要求しない。
-/

@[expose] public noncomputable section MonicPowerFamilyRelationRegularity

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze

/-- 非零指数の指定変数の冪根関係は、任意係数環上で非零因子。 -/
theorem monicPowerFamilyRelation_isSMulRegular {n : ℕ} {R : Type u} [CommRing R]
    {σ : Type v} (hn : n ≠ 0) (c : σ → R) (s : σ) :
    IsSMulRegular (MvPolynomial σ R) (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) := by
  classical
  let e := (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe s).symm).trans
    (MvPolynomial.optionEquivLeft R {t : σ // t ≠ s})
  have he : e (MvPolynomial.X s ^ n - MvPolynomial.C (c s)) =
      Polynomial.X ^ n - Polynomial.C (MvPolynomial.C (c s)) := by
    simp [e, MvPolynomial.renameEquiv]
  have h := (Polynomial.monic_X_pow_sub_C
    (MvPolynomial.C (c s) : MvPolynomial {t : σ // t ≠ s} R) hn).isRegular.left
  intro x y hxy
  apply e.injective
  apply h
  have hh := congrArg e hxy
  simpa only [smul_eq_mul, map_mul, he] using hh

end SerrePositivity.BhattScholze

end MonicPowerFamilyRelationRegularity

/-! ## 通常根添加環上の後続多項式環の自由性と忠実平坦性

既存の係数基底と直和の忠実平坦性を使う。零環・任意添字を含む。
-/

@[expose] public noncomputable section MonicPowerFamilyPolynomialFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped DirectSum
variable (n : ℕ) (σ : Type u) (τ : Type v) (R : Type w) [CommRing R]

/-- 指定冪根添加環の任意後続多項式環は元の係数環上自由。 -/
theorem monicPowerFamilyPolynomial_moduleFree (c : σ → R) (hn : 0 < n) :
    Module.Free R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  let C := MonicPowerFamilyCover n σ R c
  let := monicPowerFamilyCover_moduleFree n σ R c hn
  exact Module.Free.of_equiv ((MvPolynomial.basisMonomials τ C).repr.restrictScalars R).symm

/-- 指定冪根添加環の任意後続多項式環は元の係数環上平坦。 -/
theorem monicPowerFamilyPolynomial_moduleFlat (c : σ → R) (hn : 0 < n) :
    Module.Flat R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  let := monicPowerFamilyPolynomial_moduleFree n σ τ R c hn
  infer_instance

/-- 指定冪根添加環の任意後続多項式環は元の係数環上忠実平坦。零環も含む。 -/
theorem monicPowerFamilyPolynomial_moduleFaithfullyFlat (c : σ → R) (hn : 0 < n) :
    Module.FaithfullyFlat R (MvPolynomial τ (MonicPowerFamilyCover n σ R c)) := by
  classical
  let C := MonicPowerFamilyCover n σ R c
  let ι := τ →₀ ℕ
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all n σ R c hn
  let : Module.FaithfullyFlat R (ι →₀ C) :=
    Module.FaithfullyFlat.of_linearEquiv R (⨁ _ : ι, C) (finsuppLEquivDirectSum R C ι)
  exact Module.FaithfullyFlat.of_linearEquiv R (ι →₀ C)
    ((MvPolynomial.basisMonomials τ C).repr.restrictScalars R)

end SerrePositivity.BhattScholze

end MonicPowerFamilyPolynomialFlat

/-! ## 通常冪根添加環の完全忠実平坦性

具体的な自由・忠実平坦の結果を、既存Tor判定と剰余基底変更で接続する。
対象は未完備の通常環であり、perfectoid性や実完備化の保存は結論しない。
-/

@[expose] public noncomputable section MonicPowerFamilyCompleteFlat

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open scoped TensorProduct
variable (n : ℕ) (σ R : Type u) [CommRing R]

/-- 通常冪根添加環は任意のイデアルに関して完全平坦。
既存Torの平坦な第1変数の消滅をそのまま使う。 -/
theorem monicPowerFamilyCover_isCompletelyFlat (c : σ → R) (hn : 0 < n) (I : Ideal R) :
    IsCompletelyFlat I (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFlat n σ R c hn
  intro N _ _ _
  rw [isConcentratedInDegreeZero_derivedTensor_iff]
  intro i hi
  cases i with
  | zero => exact (Nat.lt_irrefl 0 hi).elim
  | succ i => exact torModule_subsingleton_of_flat (R := R) (MonicPowerFamilyCover n σ R c) N i

/-- 通常冪根添加環は任意イデアルに関して完全忠実平坦。零環も含む。
ここでは通常の忠実平坦性を証明済みの具体的な環にだけ適用する。 -/
theorem monicPowerFamilyCover_isCompletelyFaithfullyFlat
    (c : σ → R) (hn : 0 < n) (I : Ideal R) :
    IsCompletelyFaithfullyFlat I (MonicPowerFamilyCover n σ R c) := by
  let := monicPowerFamilyCover_moduleFaithfullyFlat_all n σ R c hn
  refine ⟨monicPowerFamilyCover_isCompletelyFlat n σ R c hn I, ?_⟩
  infer_instance

end SerrePositivity.BhattScholze

end MonicPowerFamilyCompleteFlat
