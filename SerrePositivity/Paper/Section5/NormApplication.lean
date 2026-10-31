module

public import SerrePositivity.Paper.Lemma3_5
public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField

/-!
# 長さ代数への Lemma 3.5 の適用

## 概要

§5 の設定では、正則局所環 `A` 上の有限局所代数 `T` と Theorem 2.5 の長さ代数 `(C, λ)` があり、`λ` は
`m_T C` 冪ねじれ加群の上で定義されていて、(3.9) に当たる Koszul ホモロジーの評価は `v ≥ 1` について
与えられる。Lemma 3.5（`Paper/Lemma3_5.lean`）の仮定は `λ` の定義域が `m_A C` で、有限性 `hfin` は
`v = 0` も含めて要求するので、その差を埋めて Lemma 3.5 を適用するのがこのファイルの役割である
（`normComparison_of_lengthAlgebra`）。

## 内容

- 定義域の取り替え：`m_T^N ⊆ m_A T`（`maximalIdeal_pow_le_map_of_finite`）から、同じ `λ` を `m_A C`
  冪ねじれ加群の上で使える（`NormalizedLength.restrictToBase`）。
- 有限性 `hfin`：`v ≥ 1` では (3.9) から（正次数は `0`、`0` 次は `λ(C/(z^v)C) = v^e r < ∞`）。`v = 0`
  では各 `z_j^0 = 1` なので Koszul 複体 `K(1, …, 1; C)` は可縮（`1 • 𝟙` が零ホモトピック、
  `isSupported_koszulComplex`）でホモロジーが零、したがって `λ = 0`。
- 群作用についての全射性と幾何的推移性を添えて `lemma_3_5` を適用し、ひねった複体の評価の有限性と
  共役和の一致を得る。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- **長さ代数への Lemma 3.5 の適用**：正則局所環 `A` の正則パラメータ系 `z`、`A` 上有限で剰余体が同じ
局所環 `T`、`m_T C` 冪ねじれ加群上の正規化長さ `λ` で (3.9)（`hzero`、`hquot`、`v ≥ 1`）をみたすもの、
剰余標数 `p > 0`、`A` 上 `T` に作用する有限群 `G`（`Spec T → Spec A` は全射で幾何ファイバーで
推移的）について、`z` に台をもつ完全 `T` 複体 `L` の各共役 `g^*L` の係数拡大したホモロジーの `λ` は
有限で、共役和 `Σ_g χ_T(g^*L) = Σ_g χ_C(g^*L)` が成り立つ。完備性や生成的分離性など正規化基底の
条件は要らない。`λ` の定義域を `m_A C` に取り替え、`v = 0` を含む有限性を用意して `lemma_3_5` を
呼ぶ。Lemma 3.5 の入力（層 2 の `theorem_3_1_K0`、層 3a、`lemma_3_5a_lam_finite`）に依存する。 -/
theorem normComparison_of_lengthAlgebra
    (A T C : Type u) [CommRing A] [IsRegularLocalRing A] [CommRing T] [IsLocalRing T]
    [Algebra A T] [Module.Finite A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
    {e : ℕ} (z : Fin e → A) (he : 0 < e)
    (hz : Ideal.span (Set.range z) = maximalIdeal A) (hdim : ringKrullDim A = e)
    (hres : Function.Surjective ((residue T).comp (algebraMap A T)))
    (lam : NormalizedLength C ((maximalIdeal T).map (algebraMap T C)))
    (hzero : ∀ v : ℕ, 0 < v → ∀ i : ℕ, 0 < i →
      lam.len (koszulHomologySelf (fun j ↦ algebraMap A C (z j ^ v)) i) = 0)
    (hquot : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap A C (z j ^ v))) =
        ((v ^ e * Module.finrank A T : ℕ) : ℝ≥0∞))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]
    (G : Type u) [Group G] [Fintype G] [MulSemiringAction G T] [SMulCommClass G A T]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap A T)))
    (htrans : IsGeometricallyTransitive A T G)
    (L : PerfSupp T (algebraMap A T ∘ z)) :
    (∀ (g : G) (i : ℤ), lam.len ((baseChange (algebraMap T C) (twist g L.1)).homology i) ≠ ⊤) ∧
      (∑ g : G, chiOrd (twist g L.1)) =
        ∑ g : G, chiLam lam (algebraMap T C) (twist g L.1) := by
  let lam' := lam.restrictToBase A T
  have hfin : ∀ v j : ℕ,
      lam'.len (koszulHomologySelf (fun k ↦ algebraMap A C (z k ^ v)) j) ≠ ⊤ := by
    intro v j
    by_cases hv : v = 0
    · subst v
      have hx : (fun k : Fin e ↦ algebraMap A C (z k ^ 0)) = (fun _ ↦ (1 : C)) := by
        funext k
        simp
      rw [hx]
      obtain ⟨v, hv⟩ := isSupported_koszulComplex (fun _ : Fin e ↦ (1 : C))
      obtain ⟨H⟩ := hv ⟨0, he⟩
      have h := H.homologyMap_eq (-(j : ℤ))
      simp only [one_pow, one_smul, HomologicalComplex.homologyMap_id,
        HomologicalComplex.homologyMap_zero] at h
      have hz := (IsZero.iff_id_eq_zero _).mpr h
      have := ModuleCat.subsingleton_of_isZero hz
      rw [lam'.len_eq_zero_of_subsingleton]
      exact ENNReal.zero_ne_top
    · have hv' : 0 < v := Nat.pos_of_ne_zero hv
      cases j with
      | zero =>
        have eq0 := lam'.len_congr _ _
          (koszulComplex_homology_zero_equiv (fun k ↦ algebraMap A C (z k ^ v))).some
        have hfQ := ne_of_eq_of_ne (hquot v hv') (ENNReal.natCast_ne_top _)
        exact ne_of_eq_of_ne eq0 hfQ
      | succ j =>
        change lam.len _ ≠ ⊤
        rw [hzero v hv' (j + 1) (by omega)]
        exact ENNReal.zero_ne_top
  have ht1 : (fun j ↦ algebraMap A C (z j ^ 1)) = algebraMap A C ∘ z := by
    funext j
    simp
  have hkz : ∀ i : ℕ, 0 < i →
      lam'.len (koszulHomologySelf (algebraMap A C ∘ z) i) = 0 := by
    intro i hi
    have hv := hzero 1 one_pos i hi
    rwa [ht1] at hv
  have hq : lam'.len (C ⧸ Ideal.span (Set.range (algebraMap A C ∘ z))) =
      Module.finrank A T := by
    change lam.len _ = _
    have hv := hquot 1 one_pos
    rw [ht1] at hv
    simpa only [one_pow, one_mul] using hv
  have h := lemma_3_5 hz hdim hkz hq hfin hres
    p G hsurj htrans L
  exact ⟨h.2.1, h.2.2⟩

end SerrePositivity
