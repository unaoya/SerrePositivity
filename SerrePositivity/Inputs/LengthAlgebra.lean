module

public import SerrePositivity.Descent.Lemma34Abstract
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.Koszul
public import SerrePositivity.Multiplicity
public import SerrePositivity.NormalizedLength
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# 長さ代数 `C_D` と正規化長さ `λ_D`（論文 Lemma 2.2、Theorem 2.5、Cor 2.6）

- `IsRegularNormalizationBase A D t`：Lemma 2.2 の形の正規化基底。`A` は正則完備局所環、
  `A ⊆ D` は有限かつ生成的分離、剰余体は同じ、`t` は `A` の正則パラメータ系で `D` のパラメータ系。
- `LengthAlgebraData D`：`D` 代数 `C` と正規化長さ `λ : NormalizedLength C (m_D C)`。
- `LengthAlgebraProps A D t C λ`：Theorem 2.5 の結論 (2.4)、(2.5)、(2.6)。
- `Inputs.LengthAlgebra`：Theorem 2.5 を入力束として置いた class。
- `cor_2_6`：Corollary 2.6。Lemma 3.4 の特別な場合なので、証明は Lemma 3.4 から出す（今は `sorry`）。

## 論文との差

- 生成的分離は `Algebra.IsSeparable A D`（`D` の各元の `A` 上の最小多項式が分離的）で書く。
  `A` は正則なので正規で、これは `Frac D / Frac A` の分離性と同じ。
- Lemma 2.2 の基底の具体形（`k[[t]]` または `W(k)[[t₂, …, t_h]]`）と、塔 `Λ` との両立
  （Lemma 2.3、Theorem 2.5 の「compatible Λ-action」）は入れていない。後者は Lemma 5.4 で初めて要る。
- (2.5) の右辺の Hilbert–Samuel 重複度は極限で定義しており（`hilbertSamuelMultiplicity`）、
  論文の「正で有限」は `multiplicity_pos` として別に置く。
- `λ_D` の定義域は「`m_D C` の冪で消える加群」とする。論文の `𝔡 = m_D` と同じ。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- **Lemma 2.2** の形の正規化基底 `A ⊆ D`。 -/
structure IsRegularNormalizationBase (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D]
    [IsLocalRing D] [Algebra A D] {h : ℕ} (t : Fin h → A) : Prop where
  /-- `A` は正則局所環。 -/
  regular : IsRegularLocalRing A
  /-- `A` は完備。 -/
  complete : IsAdicComplete (maximalIdeal A) A
  /-- `D` は Noether。 -/
  noetherianD : IsNoetherianRing D
  /-- `D` は整域。 -/
  domainD : IsDomain D
  /-- `D` は完備。 -/
  completeD : IsAdicComplete (maximalIdeal D) D
  /-- `A → D` は単射（`A ⊆ D`）。 -/
  injective : Function.Injective (algebraMap A D)
  /-- `D` は `A` 上有限。 -/
  finite : Module.Finite A D
  /-- 生成的分離。 -/
  separable : Algebra.IsSeparable A D
  /-- 剰余体は同じ：`A → D → D/m_D` は全射。 -/
  residue_surjective : Function.Surjective ((residue D).comp (algebraMap A D))
  /-- `dim A = h`。 -/
  dimA : ringKrullDim A = h
  /-- `dim D = h`。 -/
  dim : ringKrullDim D = h
  /-- `h > 0`。 -/
  pos : 0 < h
  /-- `t` は `A` の正則パラメータ系。 -/
  regular_params : Ideal.span (Set.range t) = maximalIdeal A
  /-- `t` は `D` のパラメータ系。 -/
  sop : IsSystemOfParameters D (algebraMap A D ∘ t)

/-- 長さ代数のデータ：`D` 代数 `C` と、`m_D C` の冪で消える `C` 加群の上の正規化長さ `λ`。 -/
structure LengthAlgebraData (D : Type u) [CommRing D] [IsLocalRing D] where
  /-- 代数 `C`。 -/
  C : Type u
  [commRing : CommRing C]
  [algebra : Algebra D C]
  /-- 正規化長さ `λ`。 -/
  lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))

attribute [instance] LengthAlgebraData.commRing LengthAlgebraData.algebra

/-- **Theorem 2.5** の結論。`C` は `D` 代数、`λ` は `m_D C` の冪で消える `C` 加群の正規化長さ。 -/
structure LengthAlgebraProps (A D : Type u) [CommRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] {h : ℕ} (t : Fin h → A) (C : Type u) [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C))) : Prop where
  /-- (2.4)：`D` の任意のパラメータ系 `z` と `v ≥ 1` で、正次数の Koszul ホモロジー `H_i(z^v; C)` の `λ` は `0`。 -/
  koszul_zero : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
    ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0
  /-- (2.5)：`λ(C/(z^v)C) = v^h e((z), D)`。 -/
  quotient_eq : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
      ENNReal.ofReal ((v : ℝ) ^ h * hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D)
  /-- (2.5) の右辺は正（有限であることは実数値なので自動）。 -/
  multiplicity_pos : ∀ (z : Fin h → D), IsSystemOfParameters D z →
    0 < hilbertSamuelMultiplicity D (Ideal.span (Set.range z)) D
  /-- (2.6)：基底の正則パラメータ `t` について `λ(C/(t^v)C) = v^h rank_A D`。 -/
  base_eq : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
      ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞)

namespace Inputs

/-- **Theorem 2.5**（正規化長さの入力）を入力束として置いた class。
Lemma 2.2 の形の基底 `A ⊆ D` で、`D` の剰余体が標数 `p > 0` の完全体なら、
長さ代数 `(C_D, λ_D)` が存在して (2.4)、(2.5)、(2.6) をみたす。

論文での根拠：標数 `p` では Monsky（Hilbert–Kunz 重複度の存在）と Roberts の Frobenius ホモロジー定理、
混標数では Cai–Lee–Ma–Schwede–Tucker の Prop. 4.0.4 / 4.0.10 / 4.0.14 と Bhatt–Scholze の perfectoid 化。 -/
class LengthAlgebra : Prop where
  exists_lengthAlgebra :
    ∀ (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D] [Algebra A D]
      {h : ℕ} (t : Fin h → A), IsRegularNormalizationBase A D t →
      ∀ (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)],
      ∃ Y : LengthAlgebraData D, LengthAlgebraProps A D t Y.C Y.lam

end Inputs

/-- **Corollary 2.6** の 1・2（有限長の基底変更）。`r = rank_A D` とすると、有限長 `A` 加群 `V` で
`λ Tor_i^A(V, C_D) = 0 (i > 0)`、`λ Tor_0^A(V, C_D) = r · length_A V`（`Tor_0 = V ⊗_A C_D`）。
Lemma 3.4 の抽象版（`lemma_3_4_of_isWeaklyRegular`）を `z = t` に適用する。 -/
theorem cor_2_6_tor (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] {h : ℕ} (t : Fin h → A) (hbase : IsRegularNormalizationBase A D t)
    (C : Type u) [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hC : LengthAlgebraProps A D t C lam)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : Module.length A V ≠ ⊤) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg (algebraMap A C) i V) = 0) ∧
      lam.len (TorAlg (algebraMap A C) 0 V) =
        (Module.finrank A D : ℝ≥0∞) * ENat.toENNReal (Module.length A V) := by
  have : IsRegularLocalRing A := hbase.regular
  have hVfl : IsFiniteLength A V := Module.length_ne_top_iff.mp hV
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal A t hbase.regular_params hbase.dimA
  have hN := exists_pow_maximalIdeal_le_map A D hbase.finite
  let lam' : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)) :=
    lam.restrict _ (fun M _ _ hM ↦ IsPowTorsion.of_pow_le hN M hM)
  have ht1 : (fun j ↦ algebraMap D C ((algebraMap A D ∘ t) j ^ 1)) = algebraMap A C ∘ t := by
    funext j
    simp [IsScalarTower.algebraMap_apply A D C]
  have ht1' : (fun j ↦ algebraMap D C (algebraMap A D (t j) ^ 1)) = algebraMap A C ∘ t := by
    funext j
    simp [IsScalarTower.algebraMap_apply A D C]
  have h39a : ∀ i : ℕ, 0 < i → lam'.len (koszulHomologySelf (algebraMap A C ∘ t) i) = 0 := by
    intro i hi
    have := hC.koszul_zero (algebraMap A D ∘ t) hbase.sop 1 one_pos i hi
    rwa [ht1] at this
  have h39b : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ t))) = Module.finrank A D := by
    have := hC.base_eq 1 one_pos
    rw [ht1'] at this
    simpa [lam'] using this
  have := lemma_3_4_of_isWeaklyRegular (algebraMap A C) t hbase.regular_params hreg lam'
    (Module.finrank A D) h39a h39b V hVfl
  exact ⟨this.1, this.2.1⟩

/-- **Corollary 2.6** の 3：`λ(C_D/𝔡 C_D) > 0`。(2.5) と `D/H` の組成列による（未証明）。 -/
theorem cor_2_6_pos (A D : Type u) [CommRing A] [IsLocalRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] {h : ℕ} (t : Fin h → A) (_hbase : IsRegularNormalizationBase A D t)
    (C : Type u) [CommRing C] [Algebra D C]
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (_hC : LengthAlgebraProps A D t C lam) :
    0 < lam.len (C ⧸ (maximalIdeal D).map (algebraMap D C)) := by
  sorry

end SerrePositivity
