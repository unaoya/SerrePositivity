module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# イデアルの冪で消える加群

`IsPowTorsion J M`：`M` がイデアル `J` のある冪で消えること。正規化長さ
（`PerfectComplex/NormalizedLength.lean`）の定義域を与える条件で、単射・全射・同型・部分加群・商で
保たれる。`J = ⊥` ならどの加群も条件をみたす（`IsPowTorsion.bot`）。
`J` が有限生成で `J ≤ √(Ann M)` なら成り立つ（`IsPowTorsion.of_le_radical_annihilator`。
台をもつ複体のホモロジーに使う）。

`IsPowTorsion.of_pow_le`：`J^N ≤ I T` なら `I C` 冪ねじれは `J C` 冪ねじれ
（正規化長さの定義域のイデアルの取り替え `NormalizedLength.restrict` に使う）。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- `M` が `J` の冪で消えること。 -/
abbrev IsPowTorsion {C : Type u} [CommRing C] (J : Ideal C) (M : Type u) [AddCommGroup M]
    [Module C M] : Prop :=
  ∃ n : ℕ, Module.IsTorsionBySet C M (J ^ n : Ideal C)

namespace IsPowTorsion

variable {C : Type u} [CommRing C] {J : Ideal C} {M N : Type u} [AddCommGroup M] [Module C M]
  [AddCommGroup N] [Module C N]

/-- `N` が `J` の冪で消えるなら、`N` に単射で入る加群 `M` も同じ冪で消える。 -/
lemma of_injective (f : M →ₗ[C] N) (hf : Function.Injective f) (hN : IsPowTorsion J N) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := hN
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_injective hf)

/-- `M` が `J` の冪で消えるなら、その全射像 `N` も同じ冪で消える。 -/
lemma of_surjective (f : M →ₗ[C] N) (hf : Function.Surjective f) (hM : IsPowTorsion J M) :
    IsPowTorsion J N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_surjective hf)

/-- 冪ねじれ性を線形同値に沿って移す。 -/
lemma of_equiv (e : M ≃ₗ[C] N) (hM : IsPowTorsion J M) : IsPowTorsion J N :=
  of_surjective e.toLinearMap e.surjective hM

/-- 冪ねじれ加群の部分加群も、同じイデアルの冪で消える。 -/
lemma submodule (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J N :=
  of_injective N.subtype N.injective_subtype hM

/-- 冪ねじれ加群の商加群も、同じイデアルの冪で消える。 -/
lemma quotient (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J (M ⧸ N) :=
  of_surjective N.mkQ N.mkQ_surjective hM

/-- 零加群は任意のイデアルについて冪ねじれである。 -/
lemma of_subsingleton [Subsingleton M] : IsPowTorsion J M :=
  ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- `J = ⊥` の冪ねじれは自明：どの加群も `⊥` 冪ねじれ。通常の長さを正規化長さ
`NormalizedLength.ordinary` として扱うときに、ねじれの仮定を満たすのに使う。 -/
lemma bot : IsPowTorsion (⊥ : Ideal C) M :=
  ⟨1, fun _ a ↦ by
    have ha : (a : C) = 0 := by simpa using a.2
    rw [ha, zero_smul]⟩

/-- `J` が有限生成で `J ≤ √(Ann M)` なら、`J` のある冪が `M` を消す。 -/
lemma of_le_radical_annihilator (hfg : J.FG) (h : J ≤ (Module.annihilator C M).radical) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hfg
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

end IsPowTorsion

/-- `J^N ≤ I T` なら、`I C` 冪ねじれは `J C` 冪ねじれ。 -/
lemma IsPowTorsion.of_pow_le {A T C : Type u} [CommRing A] [CommRing T] [CommRing C]
    [Algebra A T] [Algebra T C] [Algebra A C] [IsScalarTower A T C] {I : Ideal A} {J : Ideal T}
    (hN : ∃ N : ℕ, J ^ N ≤ I.map (algebraMap A T)) (M : Type u) [AddCommGroup M] [Module C M]
    (hM : IsPowTorsion (I.map (algebraMap A C)) M) : IsPowTorsion (J.map (algebraMap T C)) M := by
  obtain ⟨N, hN⟩ := hN
  obtain ⟨n, hn⟩ := hM
  refine ⟨N * n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  refine Set.Subset.trans ?_ hn
  rw [SetLike.coe_subset_coe, pow_mul, ← Ideal.map_pow]
  refine Ideal.pow_right_mono ?_ n
  calc (J ^ N).map (algebraMap T C) ≤ (I.map (algebraMap A T)).map (algebraMap T C) :=
        Ideal.map_mono hN
    _ = I.map (algebraMap A C) := by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end SerrePositivity
