module

public import SerrePositivity.CommutativeAlgebra.ResidueFieldExtension.General
public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # 剰余体の拡大（論文 Lemma 2.1）

## 概要

完備 Noether 局所環 `(B, 𝔟, k)` と `k` の代数閉包 `k̄` に対し、完備 Noether 局所環 `(B′, 𝔟′, k̄)` と平坦な局所準同型 `B → B′` で `𝔟B′ = 𝔟′` となるものがあり、有限 `B` 加群 `V` と `a ≥ 1` について `ℓ_{B′}((V ⊗_B B′)/𝔟′^a) = ℓ_B(V/𝔟^a V)`。したがって加群の次元・有限長・正則性・`Tor` の長さ（交点重複度）が保たれる。

## 方針

環の存在は `exists_complete_flat_local_extension_of_residueField`（CommutativeAlgebra/ResidueFieldExtension/General）を適用する。長さ・正則性・Tor の長さの保存は平坦局所拡大の一般論からここで示す（正則性は Hilbert–Samuel の多項式性と次元定理から）。

## 使われ方

Lemma 5.1 の帰着（Paper/Section5/Reduction）で、剰余体を代数閉体にするために使う。
-/

@[expose] public noncomputable section

universe u

section Lemma2_1Part

open IsLocalRing TensorProduct

namespace SerrePositivity

namespace Section2

/-- **Lemma 2.1**（剰余体の拡大）。環の実構成から保存則を導く。 -/
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
    hflat, hm, he⟩ := exists_complete_flat_local_extension_of_residueField B
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

end Lemma2_1Part
