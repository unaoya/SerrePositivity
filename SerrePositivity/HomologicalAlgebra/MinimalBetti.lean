module

public import SerrePositivity.HomologicalAlgebra.MinimalFreeResolution
public import SerrePositivity.HomologicalAlgebra.TorLES

/-! # 極小自由分解の階数と Betti 数

第1変数の Tor の長完全列を使い、極小被覆の核に沿って次数をずらす。
零次では被覆と加群の剰余体次元が等しいため、全射が同型になる。
この方法により、一般の Tor の対称性を使わずに `Tor_i(M,k)` と分解の階数を結ぶ。
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- 等しい有限長をもつ加群の間の全射は単射でもある。 -/
lemma injective_of_surjective_of_length_eq
    {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (f : V →ₗ[R] W) (hf : Function.Surjective f)
    (he : Module.length R V = Module.length R W) (hfin : Module.length R W ≠ ⊤) :
    Function.Injective f := by
  have h := Module.length_eq_add_of_exact (LinearMap.ker f).subtype f
    (Submodule.subtype_injective _) hf (LinearMap.exact_subtype_ker_map f)
  rw [he] at h
  have hz : Module.length R (LinearMap.ker f) = 0 := by
    apply ENat.add_left_injective_of_ne_top hfin
    simpa only [zero_add] using h.symm
  have := Module.length_eq_zero_iff.mp hz
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

namespace MinimalFreeResolution

variable [IsLocalRing R] [IsNoetherianRing R] (M : FGModuleCat.{u} R)

/-- 極小被覆の核に移ると、剰余体係数の Tor の次数が一つ下がる。 -/
lemma length_tor_succ (n i : ℕ) :
    Module.length R (TorModule R (i + 1) (syzygy M n) (R ⧸ maximalIdeal R)) =
      Module.length R (TorModule R i (syzygy M (n + 1)) (R ⧸ maximalIdeal R)) := by
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact_left (R ⧸ maximalIdeal R)
    (ι M n) (π M n) (ι_injective M n) (π_surjective M n) (exact_ι_π M n)
  have hdi : Function.Injective (δ i) := by
    apply (LinearMap.injective_iff_eq_zero_of_exact (hbd i)).mpr
    have := torModule_subsingleton_of_flat (R := R) (term M n) (R ⧸ maximalIdeal R) i
    ext x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  have hds : Function.Surjective (δ i) := by
    apply (LinearMap.surjective_iff_eq_zero_of_exact (hda i)).mpr
    cases i with
    | zero =>
      have hβ : Function.Injective (β 0) := by
        apply injective_of_surjective_of_length_eq _ hb
        · rw [MinimalGenerators.length_tor_zero (FGModuleCat.of R (term M n)),
            MinimalGenerators.length_tor_zero (syzygy M n), MinimalGenerators.rank_cover]
        · rw [MinimalGenerators.length_tor_zero (syzygy M n)]
          exact ENat.natCast_ne_top _
      exact (LinearMap.injective_iff_eq_zero_of_exact (hab 0)).mp hβ
    | succ i =>
      have := torModule_subsingleton_of_flat (R := R) (term M n) (R ⧸ maximalIdeal R) i
      ext x
      exact Subsingleton.elim _ _
  exact (LinearEquiv.ofBijective (δ i) ⟨hdi, hds⟩).length_eq

/-- 任意の syzygy を始点として、Tor の長さは極小自由分解の対応する項の階数に等しい。 -/
lemma length_tor_syzygy (n i : ℕ) :
    Module.length R (TorModule R i (syzygy M n) (R ⧸ maximalIdeal R)) =
      MinimalGenerators.rank (syzygy M (n + i)) := by
  induction i generalizing n with
  | zero => simpa only [Nat.add_zero] using MinimalGenerators.length_tor_zero (syzygy M n)
  | succ i ih =>
    rw [length_tor_succ]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (n + 1)

/-- `Tor_i(M,k)` の長さは、構成した極小自由分解の第 `i` 項の階数である。 -/
lemma length_tor (i : ℕ) :
    Module.length R (TorModule R i M (R ⧸ maximalIdeal R)) =
      MinimalGenerators.rank (syzygy M i) := by
  simpa only [Nat.zero_add, syzygy] using length_tor_syzygy M 0 i

/-- 構成した極小自由分解の全ての項は有限自由で、階数は Betti 数に一致する。 -/
lemma finrank_eq_length_tor (i : ℕ) :
    (Module.finrank R ((resolution M).complex.X i) : ℕ∞) =
      Module.length R (TorModule R i M (R ⧸ maximalIdeal R)) := by
  rw [length_tor]
  change (Module.finrank R (Fin (MinimalGenerators.rank (syzygy M i)) → R) : ℕ∞) = _
  simp

end MinimalFreeResolution
end SerrePositivity
