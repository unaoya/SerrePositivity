module

public import SerrePositivity.IntersectionMultiplicity.NormalizedTor
public import SerrePositivity.Inputs.RegularLocalRing
public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra
public import SerrePositivity.PerfectComplex.NormalizedLength
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Instances.ENNReal.ENatENNReal

/-!
# Lemma 3.4（論文 §3.4）

## 概要

論文 §3.4 の設定で、有限長 `A` 加群の `Tor` の正規化長さを計算する。

設定 `Setup34`：`(A, m_A, k)` は正則完備局所環で `dim A = e > 0`、剰余標数 `p`、`z` は正則パラメータ系。
`T` は `A` 上有限な局所整域で剰余体は同じ。`r = rank_A T`。`C` は `T` 代数で、正規化長さ `λ` が (3.9)

  `λ(H_i(z^v; C)) = 0 (i > 0)`、`λ(C/(z^v)C) = v^e r`（`v ≥ 1`）

をみたす。

**Lemma 3.4**：有限長 `A` 加群 `V` で `λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(V ⊗_A C) = r · ℓ_A(V)`、
すべて有限。

## 方針

一般定理 `normalizedLength_tor_of_isWeaklyRegular`（`IntersectionMultiplicity/NormalizedTor.lean`）
を、`r = rank_A T` と (3.9) の `v = 1` で適用する。`z` が弱正則列であることは A1
（`Inputs/RegularLocalRing.lean`、`sorry`）から。`λ` の定義域を `m_T C` から `m_A C` に取り替えるのに
`maximalIdeal_pow_le_map_of_finite`（`m_T^N ⊆ m_A T`）と `NormalizedLength.restrict` を使う。
Corollary 2.6 と同じ筋道で、違いは仮定の束ね方だけである。

## 規約

- 論文の `λ` は「`m_A` の冪で消える `C` 加群」の上で定義されるが、ここでは `m_T C` の冪で消える
  加群とする。`T` は `A` 上有限で剰余体が同じなので `m_A T` は `m_T` 準素であり、二つの条件は同じ。
- `Tor_i^A(C, V)` は `TorAlg (algebraMap A C) i V`、つまり `V` を分解して計算する `C` 加群。論文の
  `Tor_i^A(V, C)` と変数の順序は逆だが、Mathlib の `Tor` の規約に合わせた（`notes/PLAN.md` §1.3）。
- 論文の `V ⊗_A C` は `Tor_0^A(C, V)`、つまり `TorAlg (algebraMap A C) 0 V` で書く。`Tor_0 ≅ C ⊗_A V`
  は右完全性（`Functor.leftDerivedZeroIsoSelf`）で、別の補題にする。`TorAlg` の内部の `C ⊗[A] V` は
  `(algebraMap A C).toAlgebra` 由来の加群構造をもち、環境の `Algebra A C` 由来のものと型の上で
  食い違うので、主張には出さない。
- `ℤ_(p)` 代数という条件は、局所環で剰余標数が `p` なら自動なので書かない。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal TensorProduct

namespace SerrePositivity

/-- 論文 §3.4 の設定を束ねた構造。環の塔 `A → T → C`、正則パラメータ系 `z`、正規化長さ `λ` について、
論文の仮定をそのまま場にしたもの。`lemma_3_4` の証明で実際に使うのは `dim`、`regular_params`、
`finite`、`koszul_zero`、`quotient_eq`（`v = 1`）だけである。 -/
structure Setup34 (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    (p : ℕ) {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C))) : Prop where
  /-- `A` は `m_A` 進完備。 -/
  complete : IsAdicComplete (maximalIdeal A) A
  /-- `p` は素数。 -/
  prime : p.Prime
  /-- `A` の剰余標数は `p`。 -/
  charP : CharP (ResidueField A) p
  /-- `dim A = e`（`z` の長さ）。 -/
  dim : ringKrullDim A = e
  /-- `e > 0`。 -/
  pos : 0 < e
  /-- `z` は `A` の正則パラメータ系：`m_A` を生成する `e = dim A` 個の元。 -/
  regular_params : Ideal.span (Set.range z) = maximalIdeal A
  /-- `T` は整域。 -/
  domainT : IsDomain T
  /-- `A → T` は単射（`A ⊆ T`）。 -/
  injective : Function.Injective (algebraMap A T)
  /-- `T` は `A` 上有限生成加群。 -/
  finite : Module.Finite A T
  /-- 剰余体は同じ：`A → T → T/m_T` は全射。 -/
  residue_surjective : Function.Surjective ((residue T).comp (algebraMap A T))
  /-- (3.9) 前半：`v ≥ 1` について、正次数の Koszul ホモロジー `H_i(z^v; C)` の `λ` は `0`。 -/
  koszul_zero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
    lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0
  /-- (3.9) 後半：`λ(C/(z^v)C) = v^e · rank_A T`。 -/
  quotient_eq : ∀ v : ℕ, 0 < v →
    lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
      ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞)

/-- **Lemma 3.4**：`Setup34` の設定で、有限長 `A` 加群 `V` に対して (3.10)：
`λ(Tor_i^A(C, V)) = 0 (i > 0)`、`λ(Tor_0^A(C, V)) = rank_A T · ℓ_A(V)`（`Tor_0 = C ⊗_A V`）、
すべて有限。`z` を弱正則列にし（A1）、`λ` の定義域を `m_A C` に取り替えて、一般定理
`normalizedLength_tor_of_isWeaklyRegular` に (3.9) の `v = 1` を渡す。 -/
theorem lemma_3_4 (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    (p : ℕ) {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (S : Setup34 A T C p z lam)
    (V : Type u) [AddCommGroup V] [Module A V] (hV : Module.length A V ≠ ⊤) :
    (∀ i : ℕ, 0 < i → lam.len (TorAlg (algebraMap A C) i V) = 0) ∧
      lam.len (TorAlg (algebraMap A C) 0 V) =
        (Module.finrank A T : ℝ≥0∞) * ENat.toENNReal (Module.length A V) ∧
      (∀ i : ℕ, lam.len (TorAlg (algebraMap A C) i V) ≠ ⊤) := by
  have hVfl : IsFiniteLength A V := Module.length_ne_top_iff.mp hV
  have hreg := isWeaklyRegular_of_span_eq_maximalIdeal A z S.regular_params S.dim
  have hN : ∃ N : ℕ, (maximalIdeal T) ^ N ≤ (maximalIdeal A).map (algebraMap A T) := by
    have := S.finite
    exact maximalIdeal_pow_le_map_of_finite (R := A) T
  let lam' : NormalizedLength C ((maximalIdeal A).map (algebraMap A C)) :=
    lam.restrict _ (fun M _ _ hM ↦ IsPowTorsion.of_pow_le hN M hM)
  have hz1 : (fun j ↦ algebraMap A C (z j ^ 1)) = algebraMap A C ∘ z := by
    funext j
    simp
  have h39a : ∀ i : ℕ, 0 < i → lam'.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0 := by
    intro i hi
    have := S.koszul_zero 1 one_pos i hi
    rwa [hz1] at this
  have h39b : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) = Module.finrank A T := by
    have := S.quotient_eq 1 one_pos
    rw [hz1] at this
    simpa [lam'] using this
  exact normalizedLength_tor_of_isWeaklyRegular (algebraMap A C) z S.regular_params hreg lam'
    (Module.finrank A T) h39a h39b V hVfl

end SerrePositivity
