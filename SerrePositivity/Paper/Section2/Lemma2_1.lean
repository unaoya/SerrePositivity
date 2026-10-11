module

public import SerrePositivity.Inputs.ResidueFieldExtension
public import SerrePositivity.IntersectionMultiplicity.BaseChange
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Lemma 2.1（剰余体の拡大）

## 概要

論文 Lemma 2.1：完備 Noether 局所環 `(B, 𝔟, k)` と `k` の代数閉包 `k̄` に対して、完備 Noether
局所環 `(B', 𝔟', k̄)` と平坦な局所準同型 `B → B'` で `𝔟 B' = 𝔟'` となるものがある。有限 `B` 加群 `V` と
`a ≥ 1` について

  `ℓ_{B'}((V ⊗_B B') / 𝔟'^a (V ⊗_B B')) = ℓ_B(V / 𝔟^a V)`。

したがって加群の次元と有限長が保たれ、`B` が正則なら `B'` も正則、有限 `B` 加群 `M, N` の
`Tor` の長さ（したがって交点重複度）も保たれる。

環の存在は `Inputs.exists_complete_flat_local_extension` として引用する。
商の長さ・正則性・Tor の長さの保存は、平坦局所拡大の一般論からここで証明する。
正則性の保存は、証明済みの Hilbert–Samuel の多項式性と、未証明の次元定理に依存する。

## 使われ方

Lemma 5.1（主定理の核の場合への帰着、`notes/PLAN.md` の M1）で、剰余体を代数閉体にするために
使う。§2 の他の部分や §3–§5 の議論では使わない。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace SerrePositivity

namespace Section2

/-- **Lemma 2.1**（剰余体の拡大）。環の存在の引用から保存則を導く。 -/
theorem lemma_2_1 (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [IsAdicComplete (maximalIdeal B) B] :
    ∃ (B' : Type u) (_ : CommRing B') (_ : IsLocalRing B') (_ : IsNoetherianRing B')
      (_ : IsAdicComplete (maximalIdeal B') B') (_ : Algebra B B')
      (_ : IsLocalHom (algebraMap B B')),
      Module.Flat B B' ∧ (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' ∧
      -- 剰余体は `k` の代数閉包
      (∃ e : ResidueField B' ≃+* AlgebraicClosure (ResidueField B),
        ∀ x, e (ResidueField.map (algebraMap B B') x) =
          algebraMap (ResidueField B) (AlgebraicClosure (ResidueField B)) x) ∧
      -- 長さの保存
      (∀ (V : Type u) [AddCommGroup V] [Module B V] [Module.Finite B V] (a : ℕ), 0 < a →
        Module.length B' ((B' ⊗[B] V) ⧸ ((maximalIdeal B') ^ a • ⊤ : Submodule B' (B' ⊗[B] V))) =
          Module.length B (V ⧸ ((maximalIdeal B) ^ a • ⊤ : Submodule B V))) ∧
      -- 正則性の保存
      (IsRegularLocalRing B → IsRegularLocalRing B') ∧
      -- `Tor` の長さの保存（`M ⊗ N` が有限長のとき）
      (∀ (M N : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
        [AddCommGroup N] [Module B N] [Module.Finite B N],
        Module.length B (M ⊗[B] N) ≠ ⊤ → ∀ i : ℕ,
          torLength B i M N = torLength B' i (B' ⊗[B] M) (B' ⊗[B] N)) := by
  obtain ⟨B', bRing, bLocal, bNoetherian, bComplete, bAlg, bLocalHom,
    hflat, hm, he⟩ := Inputs.exists_complete_flat_local_extension B
      (AlgebraicClosure (ResidueField B))
  let := hflat
  refine ⟨B', bRing, bLocal, bNoetherian, bComplete, bAlg, bLocalHom,
    hflat, hm, he, ?_, ?_, ?_⟩
  · intro V _ _ _ a _
    exact samuelFunction_module_baseChange_of_map_maximalIdeal B B' hm V a
  · intro hregular
    let := hregular
    exact isRegularLocalRing_of_flat_of_map_maximalIdeal B B' hm
  · intro M N _ _ _ _ _ _ _ i
    exact (torLength_baseChange_of_map_maximalIdeal B B' hm M N i).symm

end Section2

end SerrePositivity
