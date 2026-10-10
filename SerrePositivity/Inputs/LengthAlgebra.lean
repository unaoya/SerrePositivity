module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# 長さ代数 `C_D` と正規化長さ `λ_D`（論文 Lemma 2.2、Theorem 2.5）

## 概要

論文 §2 の主要な入力は Theorem 2.5：Lemma 2.2 の形の正規化基底 `A ⊆ D`（`A` は正則完備局所環、
`D` はその上有限な完備局所整域）について、`D` 代数 `C_D` と「正規化長さ」`λ_D` の組（長さ代数）が
存在し、`D` のパラメータ系の冪 `z^v` に対して Koszul ホモロジーの `λ_D` が (2.4)、(2.5)、(2.6) の
ように計算できる、というものである。正標数では Hilbert–Kunz 重複度（Monsky）と Frobenius
ホモロジー（Roberts）、混標数では perfectoid 化（Bhatt–Scholze）と Cai–Lee–Ma–Schwede–Tucker の
結果を使うので、このプロジェクトでは証明せず、class `Inputs.LengthAlgebra` として仮定する。

## 内容

- `IsRegularNormalizationBase A D t`：Lemma 2.2 の形の正規化基底。`A` は正則完備局所環、`A ⊆ D` は
  有限かつ生成的分離、剰余体は同じ、`t` は `A` の正則パラメータ系で `D` のパラメータ系。
- `LengthAlgebraData D`：`D` 代数 `C` と正規化長さ `λ : NormalizedLength C (m_D C)` の組。
- `LengthAlgebraProps A D t C λ`：Theorem 2.5 の結論 (2.4)、(2.5)、(2.6)。
- `LengthAlgebraProps.base_values`、`base_values_one`：(2.4)、(2.6) を基底 `A` のパラメータ `t` の
  冪について書き直したもの。Corollary 2.6（`Paper/Corollary2_6.lean`）と Lemma 3.5
  （`Paper/Lemma3_5.lean`）への適用で共有する。
- `Inputs.LengthAlgebra`：Theorem 2.5 を入力束として置いた class。

## 論文との差

- 生成的分離は `Algebra.IsSeparable A D`（`D` の各元の `A` 上の最小多項式が分離的）で書く。`A` は
  正則なので正規で、これは `Frac D / Frac A` の分離性と同じ。
- Lemma 2.2 の基底の具体形（`k[[t]]` または `W(k)[[t₂, …, t_h]]`）と、塔 `Λ` との両立（Lemma 2.3、
  Theorem 2.5 の「compatible Λ-action」）は入れていない。後者は Lemma 5.4 で初めて要る。
- (2.5) の右辺の Hilbert–Samuel 重複度は極限で定義しており（`CommutativeAlgebra/Multiplicity.lean`
  の `hilbertSamuelMultiplicity`）、論文の「正で有限」は `multiplicity_pos` として別に置く。
- `λ_D` の定義域は「`m_D C` の冪で消える加群」とする。論文の `𝔡 = m_D` と同じ。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- **Lemma 2.2** の形の正規化基底 `A ⊆ D`：完備な Noether 局所整域 `D` に対して、Lemma 2.2 は
`D` の部分環 `A` で正則完備局所環であり、`D` が `A` 上有限かつ生成的分離で、剰余体が同じになるものと、
`A` の正則パラメータ系 `t` で `D` のパラメータ系にもなるものの存在を主張する。この構造はその結論を
仮定として書いたもので、Theorem 2.5 の前提になる。`h = dim A = dim D` は `t` の長さ。 -/
structure IsRegularNormalizationBase (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D]
    [IsLocalRing D] [Algebra A D] {h : ℕ} (t : Fin h → A) : Prop where
  /-- `A` は正則局所環。 -/
  regular : IsRegularLocalRing A
  /-- `A` は `m_A` 進完備。 -/
  complete : IsAdicComplete (maximalIdeal A) A
  /-- `D` は Noether 環。 -/
  noetherianD : IsNoetherianRing D
  /-- `D` は整域。 -/
  domainD : IsDomain D
  /-- `D` は `m_D` 進完備。 -/
  completeD : IsAdicComplete (maximalIdeal D) D
  /-- `A → D` は単射（`A ⊆ D`）。 -/
  injective : Function.Injective (algebraMap A D)
  /-- `D` は `A` 上有限生成加群。 -/
  finite : Module.Finite A D
  /-- 生成的分離：`D` の各元の `A` 上の最小多項式が分離的。 -/
  separable : Algebra.IsSeparable A D
  /-- 剰余体は同じ：`A → D → D/m_D` は全射。 -/
  residue_surjective : Function.Surjective ((residue D).comp (algebraMap A D))
  /-- `dim A = h`。 -/
  dimA : ringKrullDim A = h
  /-- `dim D = h`（`D` は `A` 上有限なので `dim A` と等しい）。 -/
  dim : ringKrullDim D = h
  /-- `h > 0`（次元 `0` の場合は主定理の設定に現れない）。 -/
  pos : 0 < h
  /-- `t` は `A` の正則パラメータ系：`m_A` を生成する `h = dim A` 個の元。 -/
  regular_params : Ideal.span (Set.range t) = maximalIdeal A
  /-- `t` の `D` での像は `D` のパラメータ系：`√(t D) = m_D`。 -/
  sop : IsSystemOfParameters D (algebraMap A D ∘ t)

/-- 長さ代数のデータ：`D` 代数 `C`（論文の `C_D`。正標数では `D` の perfection、混標数では
perfectoid 化）と、`m_D C` の冪で消える `C` 加群の上の正規化長さ `λ`（論文の `λ_D`）。性質は
`LengthAlgebraProps` に分けてある。 -/
structure LengthAlgebraData (D : Type u) [CommRing D] [IsLocalRing D] where
  /-- 代数 `C` の台の型。 -/
  C : Type u
  /-- `C` の可換環構造。 -/
  [commRing : CommRing C]
  /-- `C` の `D` 代数構造。 -/
  [algebra : Algebra D C]
  /-- 正規化長さ `λ`、定義域は `m_D C` 冪ねじれ加群。 -/
  lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))

attribute [instance] LengthAlgebraData.commRing LengthAlgebraData.algebra

/-- **Theorem 2.5** の結論。`D` 代数 `C` と `m_D C` 冪ねじれ加群上の正規化長さ `λ` について、`D` の
パラメータ系 `z` とその冪 `z^v = (z_1^v, …, z_h^v)`（`v ≥ 1`）の Koszul ホモロジーの `λ` が次のように
計算できること。直観的には、`C` 上で `z^v` が「正則列のように振る舞い」、`λ(C/(z^v)C)` が
Hilbert–Samuel 重複度で測れる、ということである。 -/
structure LengthAlgebraProps (A D : Type u) [CommRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] {h : ℕ} (t : Fin h → A) (C : Type u) [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))) : Prop where
  /-- (2.4)：`D` の任意のパラメータ系 `z` と `v ≥ 1` について、正次数の Koszul ホモロジー
  `H_i(z^v; C)` の `λ` は `0`。 -/
  koszul_zero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
    ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0
  /-- (2.5)：`λ(C/(z^v)C) = v^h · e(z; D)`（`e` は Hilbert–Samuel 重複度、
  `CommutativeAlgebra/Multiplicity.lean`）。 -/
  quotient_eq : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
      ENNReal.ofReal ((v : ℝ) ^ h * hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D)
  /-- (2.5) の右辺の重複度は正（有限であることは実数値なので自動）。`hilbertSamuelMultiplicity` は
  極限で定義してあり、その正値性はここで仮定する。 -/
  multiplicity_pos : ∀ (z : Fin h → D), IsSystemOfParameters D z →
    0 < hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D
  /-- (2.6)：基底の正則パラメータ系 `t` については `λ(C/(t^v)C) = v^h · rank_A D`。`e(t; D) = rank_A D`
  （`D` が `A` 上有限で `e(t; A) = 1`）による。 -/
  base_eq : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
      ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞)

section preparation

variable {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
  [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
  {h : ℕ} {t : Fin h → A}

/-- (2.4) と (2.6) を、基底 `A` のパラメータ系 `t` の冪 `t^v` について、`A → C` の像で書き直したもの：
`λ(H_i(t^v; C)) = 0 (i > 0)` と `λ(C/(t^v)C) = v^h · rank_A D`。`t` の `D` での像がパラメータ系で
あること（`hsop`）を使い、`algebraMap D C ∘ algebraMap A D = algebraMap A C` で書き換えるだけ。
Corollary 2.6 と Lemma 3.5 で、`NormalizedTor.lean` の仮定 (3.9) の形にするために使う。 -/
theorem LengthAlgebraProps.base_values
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hC : LengthAlgebraProps A D t C lam)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (v : ℕ) (hv : 0 < v) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (t j ^ v)) i) = 0) ∧
    lam.len
      (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (t j ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞) := by
  have heq : (fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v)) =
      (fun j ↦ algebraMap A C (t j ^ v)) := by
    funext j
    simp [IsScalarTower.algebraMap_apply A D C]
  constructor
  · intro i hi
    have hz := hC.koszul_zero (algebraMap A D ∘ t) hsop v hv i hi
    rw [heq] at hz
    exact hz
  · have hq := hC.base_eq v hv
    change lam.len (C ⧸ Ideal.span
      (Set.range fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v))) = _ at hq
    rw [heq] at hq
    exact hq

/-- `base_values` の `v = 1` の場合：`λ(H_i(t; C)) = 0 (i > 0)` と `λ(C/tC) = rank_A D`。 -/
theorem LengthAlgebraProps.base_values_one
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hC : LengthAlgebraProps A D t C lam)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (algebraMap A C ∘ t) i) = 0) ∧
    lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ t))) =
      Module.finrank A D := by
  have ht : (fun j ↦ algebraMap A C (t j ^ 1)) = algebraMap A C ∘ t := by
    funext j
    simp
  have hv := hC.base_values hsop 1 one_pos
  rw [ht] at hv
  simpa only [one_pow, one_mul] using hv

end preparation

namespace Inputs

/-- **Theorem 2.5**（長さ代数の存在）を入力束として置いた class。Lemma 2.2 の形の基底 `A ⊆ D` で、
`D` の剰余体が標数 `p > 0` の完全体なら、長さ代数 `(C_D, λ_D)` が存在して (2.4)、(2.5)、(2.6) を
みたす。

論文での根拠：標数 `p` では Monsky（Hilbert–Kunz 重複度の存在）と Roberts の Frobenius ホモロジー
定理、混標数では Cai–Lee–Ma–Schwede–Tucker の Prop. 4.0.4 / 4.0.10 / 4.0.14 と Bhatt–Scholze の
perfectoid 化。このプロジェクトでは証明せず、主定理の仮定として引き回す。 -/
class LengthAlgebra : Prop where
  /-- 正規化基底 `A ⊆ D`（`IsRegularNormalizationBase`）と、`D` の剰余体が標数 `p` の完全体で
  あることから、Theorem 2.5 の性質をみたす長さ代数が存在する。 -/
  exists_lengthAlgebra :
    ∀ (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
      {h : ℕ} (t : Fin h → A), IsRegularNormalizationBase A D t →
      ∀ (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)],
      ∃ Y : LengthAlgebraData D, LengthAlgebraProps A D t Y.C Y.lam

end Inputs

end SerrePositivity
