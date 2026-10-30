module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField

/-!
# イデアルの冪で消える加群

## 概要

加群 `M` がイデアル `J` のある冪 `J^n` で消えること（`J^n M = 0`）を `IsPowTorsion J M` と書く。
これは正規化長さ（`PerfectComplex/NormalizedLength.lean`）の定義域を与える条件である。論文の
正規化長さ `λ` は「`m` の冪で消える加群」の上でだけ加法的なので、`λ` を使う議論では、扱う加群が
この条件をみたすことをつねに確かめる必要がある。このファイルはそのための補題を集める。

## 内容

- 条件は単射・全射・線形同値・部分加群・商で保たれ、零加群はつねにみたす。いずれも
  「`M` が `J^n` で消える ⇔ `J^n ⊆ Ann M`」と、零化イデアルが単射で大きく・全射で大きくなる
  ことによる。
- `J = ⊥` ならどの加群もみたす（`bot`）。通常の長さを正規化長さの特別な場合として扱うとき
  （`NormalizedLength.ordinary`）に、ねじれの仮定を自動的に満たすために使う。
- `J` が有限生成で `J ⊆ √(Ann M)` なら成り立つ（`of_le_radical_annihilator`）。有限生成イデアルが
  根基に入れば冪が入る、という Mathlib の事実による。台をもつ複体のホモロジーに使う。
- 定義域のイデアルの取り替え（`of_pow_le`）：環の塔 `A → T → C` で `J^N ⊆ I T` なら、`I C` の冪で
  消える加群は `J C` の冪でも消える。論文では `λ` を `m_D C` の冪ねじれ加群の上で定義する一方、
  Lemma 3.4・3.5 では `m_A C` の冪ねじれを扱う（`A ⊆ D` が有限なら `m_D^N ⊆ m_A D`）ので、
  この補題で定義域を取り替える（`NormalizedLength.restrict`）。
-/

@[expose] public section

universe u

namespace SerrePositivity

/-- `M` がイデアル `J` のある冪で消えること：`J^n M = 0` となる `n` がある。Mathlib の
`Module.IsTorsionBySet`（集合の元すべてが `M` を消す）を `J^n` に適用した形で、`J^n ⊆ Ann M` と
同値である。正規化長さ `NormalizedLength C J` の定義域の条件。 -/
abbrev IsPowTorsion {C : Type u} [CommRing C] (J : Ideal C) (M : Type u) [AddCommGroup M]
    [Module C M] : Prop :=
  ∃ n : ℕ, Module.IsTorsionBySet C M (J ^ n : Ideal C)

namespace IsPowTorsion

variable {C : Type u} [CommRing C] {J : Ideal C} {M N : Type u} [AddCommGroup M] [Module C M]
  [AddCommGroup N] [Module C N]

/-- `N` が `J` の冪で消え、`f : M → N` が単射なら、`M` も同じ冪で消える。単射なら零化イデアルは
大きくなる（`Ann N ⊆ Ann M`）ことによる。 -/
lemma of_injective (f : M →ₗ[C] N) (hf : Function.Injective f) (hN : IsPowTorsion J N) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := hN
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_injective hf)

/-- `M` が `J` の冪で消え、`f : M → N` が全射なら、`N` も同じ冪で消える。全射なら零化イデアルは
大きくなる（`Ann M ⊆ Ann N`）ことによる。 -/
lemma of_surjective (f : M →ₗ[C] N) (hf : Function.Surjective f) (hM : IsPowTorsion J M) :
    IsPowTorsion J N := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator] at hn ⊢
  exact hn.trans (f.annihilator_le_of_surjective hf)

/-- 線形同値 `e : M ≃ N` で冪ねじれの条件は移る（`of_surjective` の特別な場合）。 -/
lemma of_equiv (e : M ≃ₗ[C] N) (hM : IsPowTorsion J M) : IsPowTorsion J N :=
  of_surjective e.toLinearMap e.surjective hM

/-- 冪ねじれ加群の部分加群は、同じ冪で消える（包含が単射）。 -/
lemma submodule (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J N :=
  of_injective N.subtype N.injective_subtype hM

/-- 冪ねじれ加群の商加群は、同じ冪で消える（商への射影が全射）。 -/
lemma quotient (hM : IsPowTorsion J M) (N : Submodule C M) : IsPowTorsion J (M ⧸ N) :=
  of_surjective N.mkQ N.mkQ_surjective hM

/-- 零加群はどんなイデアルについても冪ねじれである（`n = 0`、`J^0 = ⊤` でも零加群は消える）。 -/
lemma of_subsingleton [Subsingleton M] : IsPowTorsion J M :=
  ⟨0, fun _ _ ↦ Subsingleton.elim _ _⟩

/-- `J = ⊥` のときはどの加群も冪ねじれである：`⊥^1 = ⊥` で、`0 • x = 0` だから。通常の長さ
`Module.length` を `J = ⊥` の正規化長さ `NormalizedLength.ordinary` とみなし、正規化長さの一般定理
（写像錐についての加法性など）を通常の長さに特殊化するときに、ねじれの仮定をこれで満たす
（`PerfectComplex/OrdinaryEuler.lean`）。 -/
lemma bot : IsPowTorsion (⊥ : Ideal C) M :=
  ⟨1, fun _ a ↦ by
    have ha : (a : C) = 0 := by simpa using a.2
    rw [ha, zero_smul]⟩

/-- `J` が有限生成で `J ⊆ √(Ann M)`（`J` の各元のある冪が `M` を消す）なら、`J` のある冪が `M` を
消す。有限個の生成元それぞれの冪が `Ann M` に入るので、十分大きい冪で `J^n ⊆ Ann M` となる
（Mathlib の `Ideal.exists_pow_le_of_le_radical_of_fg`）。台をもつ複体のホモロジーが冪ねじれで
あること（`PerfectComplex/Support.lean`、`PerfectComplex/NormalizedEuler.lean`）に使う。 -/
lemma of_le_radical_annihilator (hfg : J.FG) (h : J ≤ (Module.annihilator C M).radical) :
    IsPowTorsion J M := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h hfg
  refine ⟨n, ?_⟩
  rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe]
  exact hn

end IsPowTorsion

/-- 環の塔 `A → T → C` と、`A` のイデアル `I`、`T` のイデアル `J` について、`J^N ⊆ I T` なら、
`I C` の冪で消える `C` 加群は `J C` の冪でも消える：`(J C)^{N n} = (J^N) C ⊆ (I T) C = I C` の `n` 乗が
`M` を消すから。論文で正規化長さ `λ` の定義域を `m_D C` から `m_A C` に取り替えるとき
（`A ⊆ D` が有限なら `m_D^N ⊆ m_A D`、`LocalAlgebra.lean` の `maximalIdeal_pow_le_map_of_finite`）に、
`NormalizedLength.restrict` と組み合わせて使う。 -/
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
