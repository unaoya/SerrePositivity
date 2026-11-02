module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Tower

/-!
# Lemma 2.4（零長さの極限）

## 概要

論文 Lemma 2.4：すべての加群が `m_A` の固定した冪で消されるとき、塔の正規化長さ `λ_∞` について

1. 長さ `0` の加群の和・直和・有向余極限は長さ `0`、
2. 増大列の合併で `λ_∞(⋃ V_a) = sup λ_∞(V_a)`、
3. `λ_∞(V_a) → 0` なら `λ_∞(lim→ V_a) = 0`（遷移写像の単射性は不要）。

証明は論文どおり、上限の性質 (2.3)（`towerLength_hasSup`）と加法性・単調性だけを使う。一般の
正規化長さに対する形は `PerfectComplex/SupProperty.lean` にあり、ここではそれを `λ_∞` に適用する。
-/

@[expose] public section

universe u

open IsLocalRing
open scoped ENNReal DirectSum

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)

include ht

/-- **Lemma 2.4 (1)、和**：`m_A Λ` 冪ねじれ加群 `M` の部分加群の族で各 `λ_∞(V_i) = 0` なら
`λ_∞(⨆ V_i) = 0`。 -/
theorem lemma_2_4_iSup (M : Type u) [AddCommGroup M] [Module (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) {ι : Type*}
    (V : ι → Submodule (Tower A t p) M) (hV : ∀ i, towerLengthFun A t p (V i) = 0) :
    towerLengthFun A t p (⨆ i, V i : Submodule (Tower A t p) M) = 0 :=
  NormalizedLength.len_iSup_eq_zero (towerLength_hasSup A t p ht) hM V hV

/-- **Lemma 2.4 (1)、直和**：各 `V_i` が `(m_A Λ)^n` で消え `λ_∞(V_i) = 0` なら
`λ_∞(⨁ V_i) = 0`。 -/
theorem lemma_2_4_directSum {ι : Type u} (V : ι → Type u)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (Tower A t p) (V i)] (n : ℕ)
    (hn : ∀ i, Module.IsTorsionBySet (Tower A t p) (V i) (towerMaxIdeal A t p ^ n : Ideal _))
    (hV : ∀ i, towerLengthFun A t p (V i) = 0) :
    towerLengthFun A t p (⨁ i, V i) = 0 :=
  NormalizedLength.len_directSum_eq_zero (towerLength_hasSup A t p ht) V n hn hV

/-- **Lemma 2.4 (2)、増大列の合併**：有向な部分加群の族で `λ_∞(⨆ V_i) = ⨆ λ_∞(V_i)`。 -/
theorem lemma_2_4_iSup_of_directed (M : Type u) [AddCommGroup M] [Module (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M) {ι : Type*} [Nonempty ι]
    (V : ι → Submodule (Tower A t p) M) (hdir : Directed (· ≤ ·) V) :
    towerLengthFun A t p (⨆ i, V i : Submodule (Tower A t p) M) =
      ⨆ i, towerLengthFun A t p (V i) :=
  NormalizedLength.len_iSup_of_directed (towerLength_hasSup A t p ht) hM V hdir

/-- **Lemma 2.4 (3)、有向余極限**：各 `V_i` が `(m_A Λ)^n` で消え `λ_∞(V_i) → 0` なら
`λ_∞(lim→ V_i) = 0`。遷移写像の単射性は要らない。 -/
theorem lemma_2_4_directLimit {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    [DecidableEq ι] (V : ι → Type u) [∀ i, AddCommGroup (V i)] [∀ i, Module (Tower A t p) (V i)]
    (f : ∀ i j, i ≤ j → V i →ₗ[Tower A t p] V j) (n : ℕ)
    (hn : ∀ i, Module.IsTorsionBySet (Tower A t p) (V i) (towerMaxIdeal A t p ^ n : Ideal _))
    (hlim : Filter.Tendsto (fun i ↦ towerLengthFun A t p (V i)) Filter.atTop (nhds 0)) :
    towerLengthFun A t p (Module.DirectLimit V f) = 0 :=
  NormalizedLength.len_directLimit_eq_zero_of_tendsto (towerLength_hasSup A t p ht) V f n hn hlim

end Section2

end SerrePositivity
