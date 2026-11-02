module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.Paper.Section5.Reduction
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# 主張

## 概要

論文 *Positivity of Serre's Intersection Multiplicity*（OpenAI、2026-09-23）の主定理 Theorem 1.1 と、
Lemma 5.1 で帰着した後の核の場合を述べる。主定理と核の場合はいずれも
名前付きの引用入力から証明し、自身の `sorry` は持たない。

- `main_statement`：Theorem 1.1。正則局所環 `(R, m)` と `0` でない有限生成加群 `M`、`N` について、
  `M ⊗_R N` が有限長かつ `dim M + dim N = dim R` なら `χ^R(M, N) > 0`。交点重複度 `χ` は
  `IntersectionMultiplicity/Basic.lean`。
- `core_statement`：Lemma 5.1 による帰着先。`R` が完備で剰余体が標数 `p > 0` の代数閉体、
  `M = R/P`、`N = R/Q` が正次元の素イデアル商、`P + Q` が `m` 準素の場合。

## 方針

証明は帰着（完備化・剰余体の拡大・素イデアル商へのデヴィサージュ）と
核（§5 の正値性の議論、`Paper/Section5/`）で与える。
`Paper/Section5/Setup.lean` は素イデアル商から正規化基底とガロア拡大を構成し、長さ代数、
群作用、二つの比較へ接続する。`core_statement` 自身の `sorry` は除去済み。
`Paper/Section5/Reduction.lean` は、核の場合を任意の有限生成加群へ広げ（デヴィサージュ）、
Lemma 2.1 と平坦局所拡大の保存則で剰余体の代数閉性を外し、完備化で一般の環へ広げる。
剰余標数零の場合は Serre の対角線論法（`IntersectionMultiplicity/EqualCharZeroPositivity.lean`）による。
§2 の長さ代数の存在などの引用入力は残る。
-/

public section

universe u

namespace SerrePositivity

open TensorProduct

variable (R : Type u) [CommRing R]

/-- **Theorem 1.1**（名前付き引用入力から証明）：`(R, m)` を正則局所環、`M`、`N` を
`0` でない有限生成 `R` 加群とする。
`ℓ_R(M ⊗_R N) < ∞`（幾何的には `Supp M ∩ Supp N` が閉点だけ）かつ `dim M + dim N = dim R`（固有な
交わり）なら `χ^R(M, N) > 0`。Serre の正値性予想の主張。
正の剰余標数では核心定理への帰着を、剰余標数零では Serre の対角線論法（証明済み）を用いる。 -/
theorem main_statement [IsRegularLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField R)
  rcases CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R) p with hprime | rfl
  · let : Fact p.Prime := ⟨hprime⟩
    exact Section5.positivity_of_residueCharP R p M N hfin hdim
  · let : CharZero (IsLocalRing.ResidueField R) := CharP.charP_to_charZero _
    exact Section5.positivity_of_residueCharZero R M N hfin hdim

/-- **Lemma 5.1 の帰着先**（既存の引用入力から証明）：`R` は完備で剰余体は標数 `p > 0` の代数閉体、`P`、`Q` は
素イデアルで `R/P`、`R/Q` は正次元、`dim R/P + dim R/Q = dim R`、`P + Q` は `m` 準素
（`√(P + Q) = m`、すなわち `R/P ⊗ R/Q` が有限長）。このとき `χ^R(R/P, R/Q) > 0`。論文の §5 は
この場合を扱う。 -/
theorem core_statement [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  exact Section5.core_of_complete_algClosed R p P Q hP hQ hsum hprimary

end SerrePositivity
