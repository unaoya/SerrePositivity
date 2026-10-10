module

public import SerrePositivity.Paper.Lemma3_5
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra

/-!
# 長さ代数への補題3.5の適用

正則局所環上の有限局所代数 `A → T` と定理2.5の長さ代数 `(C, λ)` を、補題3.5の仮定に合わせる。
`m_T` のある冪が `m_A T` に入ることから、同じ長さを `m_A C` の冪ねじれ加群上で使える。
パラメータの正の冪では Koszul ホモロジーの消滅と商の長さの公式を用いる。
冪が零の場合には各パラメータが `1` になるため、Koszul 複体の可縮性から評価の有限性を得る。

群作用についての全射性と幾何的推移性を併せて補題3.5を適用し、
ひねった複体の評価の有限性と共役和の一致を得る。このファイルはその適用部分を証明する。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

/-- Koszul ホモロジーの消滅と商の長さ、有限性、パラメータ系、剰余体への全射を
個別に受け取り、補題3.5を適用する。
完備性や生成的分離性を含む正規化基底の構成条件は要求しない。
有限拡大による極大イデアルの冪の包含を使い、長さの値を変えずに加法性の対象を `m_A C` の冪ねじれへ制限する。
群作用の幾何的推移性などを仮定し、各ひねりのホモロジー評価の有限性と通常・正規化共役和の一致を得る。
補題3.5とその入力に依存する。 -/
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
