module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.CommutativeAlgebra.PowTorsion

/-!
# 有限長加群の `Tor` の冪ねじれ性

局所環 `A` 上の有限長加群 `V` について、`Tor_i^A(C, V)`（`TorAlg φ i V`）は `m_A C`（`m_A` の `C` への
拡大）のある冪で消える（`torAlg_isPowTorsion`）。有限長加群は `m_A` の冪 `m_A^n` で消え
（`FiniteLength.lean`）、`V` を消す元は `Tor` も消す（`HomologicalAlgebra/Tor.lean` の
`torAlg_smul_eq_zero`）ことによる。これで `Tor_i^A(C, V)` が正規化長さ `λ`（定義域は `m_A C` 冪ねじれ
加群）で測れることが保証され、Lemma 3.4 と Corollary 2.6
（`IntersectionMultiplicity/NormalizedTor.lean`）で使う。
-/

@[expose] public section

universe u

open IsLocalRing

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

variable [IsLocalRing A]

/-- 局所環 `A` 上の有限長加群 `V` について、`Tor_i^A(C, V)` は `(m_A C)^n` で消える `n` がある。
`V` が `m_A^n` で消えるので、`m_A^n` の各元 `a` について `φ(a)` が `Tor` を消し
（`torAlg_smul_eq_zero`）、`(m_A C)^n = (m_A^n) C` はそのような `φ(a)` で生成されるから。 -/
lemma torAlg_isPowTorsion (i : ℕ) (V : Type u) [AddCommGroup V] [Module A V]
    (hV : IsFiniteLength A V) : IsPowTorsion ((maximalIdeal A).map φ) (TorAlg φ i V) := by
  obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, ← Ideal.map_pow, Ideal.map,
    SetLike.coe_subset_coe, Ideal.span_le]
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Module.mem_annihilator]
  intro x
  exact torAlg_smul_eq_zero φ i V a (fun v ↦ @hn v ⟨a, ha⟩) x

end SerrePositivity
