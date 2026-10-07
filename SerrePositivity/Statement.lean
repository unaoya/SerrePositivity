module

public import SerrePositivity.EulerChar
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# 主張

論文 *Positivity of Serre's Intersection Multiplicity*（OpenAI、2026-09-23）の Theorem 1.1 と、
Lemma 5.1 で帰着した後の核の場合を、証明なしの主張として置く。

- `main_statement`：Theorem 1.1。
- `core_statement`：`R` が完備で剰余体が標数 `p > 0` の代数閉体、`M = R/P`、`N = R/Q` が
  正次元の素イデアル商、`P + Q` が `m` 準素の場合。

証明は `notes/PLAN.md` の M1（帰着）と M3（核）で与える。それまで `sorry` のまま置く。
-/

public section

universe u

namespace SerrePositivity

open TensorProduct

variable (R : Type u) [CommRing R]

/-- **Theorem 1.1**。`(R, m)` を正則局所環、`M, N` を `0` でない有限生成 `R` 加群とする。
`length_R (M ⊗_R N) < ∞` かつ `dim M + dim N = dim R` なら `χ^R(M, N) > 0`。 -/
theorem main_statement [IsRegularLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  sorry

/-- **Lemma 5.1 の帰着先**。`R` は完備で剰余体は標数 `p > 0` の代数閉体、
`P, Q` は素イデアルで `R/P`、`R/Q` は正次元、`dim R/P + dim R/Q = dim R`、
`P + Q` は `m` 準素。このとき `χ^R(R/P, R/Q) > 0`。 -/
theorem core_statement [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  sorry

end SerrePositivity
