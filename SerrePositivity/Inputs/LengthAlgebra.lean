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
結果を使うので、このプロジェクトでは証明せず、名前付きの `sorry` 定理 `Inputs.exists_lengthAlgebra` として引用する。

## 内容

`Inputs.exists_lengthAlgebra` の前提はすべて個別の引数で書く。結論も環 `C`、環構造、代数構造、
正規化長さ `λ` を存在量化し、(2.4)、(2.5)、重複度の正値性、(2.6) の四つの性質を連言で返す。
適用先では必要な性質だけを個別の引数として受け取る。設定をまとめる構造体は用いない。

`lengthAlgebra_base_values` と `lengthAlgebra_base_values_one` は、明示された (2.4)、(2.6)
だけを使い、基底 `A` のパラメータの冪についての評価に書き換える。

## 論文との差

- 生成的分離は `Algebra.IsSeparable A D`（`D` の各元の `A` 上の最小多項式が分離的）で書く。`A` は
  正則なので正規で、これは `Frac D / Frac A` の分離性と同じ。
- Lemma 2.2 の基底の具体形（`k[[t]]` または `W(k)[[t₂, …, t_h]]`）と、塔 `Λ` との両立（Lemma 2.3、
  Theorem 2.5 の「compatible Λ-action」）は入れていない。後者は Lemma 5.4 で初めて要る。
- (2.5) の右辺の Hilbert–Samuel 重複度は極限で定義しており（`CommutativeAlgebra/Multiplicity.lean`
  の `hilbertSamuelMultiplicity`）、論文の「正で有限」は 独立した結論として明記する。
- `λ_D` の定義域は「`m_D C` の冪で消える加群」とする。論文の `𝔡 = m_D` と同じ。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

section preparation

variable {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
  [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
  {h : ℕ} {t : Fin h → A}

/-- (2.4) と (2.6) を、基底 `A` のパラメータ系 `t` の冪 `t^v` について、`A → C` の像で書き直したもの：
`λ(H_i(t^v; C)) = 0 (i > 0)` と `λ(C/(t^v)C) = v^h · rank_A D`。`t` の `D` での像がパラメータ系で
あること（`hsop`）を使い、`algebraMap D C ∘ algebraMap A D = algebraMap A C` で書き換えるだけ。
Corollary 2.6 と Lemma 3.5 で、`NormalizedTor.lean` の仮定 (3.9) の形にするために使う。 -/
theorem lengthAlgebra_base_values
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
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
    have hz := hzero (algebraMap A D ∘ t) hsop v hv i hi
    rw [heq] at hz
    exact hz
  · have hq := hbase v hv
    change lam.len (C ⧸ Ideal.span
      (Set.range fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ v))) = _ at hq
    rw [heq] at hq
    exact hq

/-- `base_values` の `v = 1` の場合：`λ(H_i(t; C)) = 0 (i > 0)` と `λ(C/tC) = rank_A D`。 -/
theorem lengthAlgebra_base_values_one
    {lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))}
    (hzero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
        ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) :
    (∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (algebraMap A C ∘ t) i) = 0) ∧
    lam.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ t))) =
      Module.finrank A D := by
  have ht : (fun j ↦ algebraMap A C (t j ^ 1)) = algebraMap A C ∘ t := by
    funext j
    simp
  have hv := lengthAlgebra_base_values hzero hbase hsop 1 one_pos
  rw [ht] at hv
  simpa only [one_pow, one_mul] using hv

end preparation

namespace Inputs

/-- **Theorem 2.5**（長さ代数の存在）の未証明の存在定理。Lemma 2.2 の形の基底 `A ⊆ D` で、
`D` の剰余体が標数 `p > 0` の完全体なら、長さ代数 `(C_D, λ_D)` が存在して (2.4)、(2.5)、(2.6) を
みたす。

論文での根拠：標数 `p` では Monsky（Hilbert–Kunz 重複度の存在）と Roberts の Frobenius ホモロジー
定理、混標数では Cai–Lee–Ma–Schwede–Tucker の Prop. 4.0.4 / 4.0.10 / 4.0.14 と Bhatt–Scholze の
perfectoid 化。このプロジェクトでは名前付きの `sorry` 定理として置き、利用する証明から明示的に呼ぶ。 -/
theorem exists_lengthAlgebra
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    [Algebra.IsSeparable A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra D C)
      (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))),
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
        ∀ i : ℕ, 0 < i →
          lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
        lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
          ENNReal.ofReal ((v : ℝ) ^ h * hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D)) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        0 < hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D) ∧
      (∀ v : ℕ, 0 < v →
        lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
          ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞)) := by
  sorry

end Inputs

end SerrePositivity
