module

public import SerrePositivity.Asymptotic.SequenceHomology
public import SerrePositivity.LengthAlgebra.Ordinary
public import SerrePositivity.Paper.Lemma3_5.Ordinary
public import SerrePositivity.Inputs.LengthAlgebra

/-!
# §4 のホモロジー評価に必要な Koszul 有限性

通常の長さでは Noether 性とパラメータ商の Artin 性から有限性を得る。
正規化長さでは (2.4) の消滅と (2.6) の有限な商の値を使う。
§2 の代数の存在定理そのものには依存せず、その二つの性質からの接続を証明する。
-/

@[expose] public section

universe u

namespace SerrePositivity.Section4

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

/-- 有限な基底変更で得た環上でも、§4 の通常の長さの有限性入力を供給できる。 -/
lemma ordinary_koszul_pow_finite_of_finite
    {A T : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing T] [Algebra A T] [Module.Finite A T]
    {e : ℕ} (z : Fin e → A)
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (v : ℕ) (i : ℤ) :
    (NormalizedLength.ordinary T).len
      ((koszulComplex (fun j ↦ (algebraMap A T (z j)) ^ v)).homology i) ≠ ⊤ := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite A T
  have := isArtinianRing_quotient_span_of_finite A T z hz
  exact ordinary_koszul_pow_finite (algebraMap A T ∘ z) v i

/-- 正の Koszul ホモロジーの長さが零で、第零商の長さが有限なら、全次数で有限。 -/
lemma normalized_koszul_finite {C : Type u} [CommRing C] {J : Ideal C}
    (lam : NormalizedLength C J) {e : ℕ} (x : Fin e → C)
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf x i) = 0)
    (hquot : lam.len (C ⧸ Ideal.span (Set.range x)) ≠ ⊤) (i : ℤ) :
    lam.len ((koszulComplex x).homology i) ≠ ⊤ :=
  LengthAlgebra.koszul_finite_of_zero_positive lam x hzero hquot i

/-- 非負の homological 次数での有限性を全整数次数に読み替える共通補題。 -/
lemma normalized_koszul_finite_of_homologySelf
    {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)
    {e : ℕ} (x : Fin e → C)
    (hfin : ∀ j : ℕ, lam.len (koszulHomologySelf x j) ≠ ⊤) (i : ℤ) :
    lam.len ((koszulComplex x).homology i) ≠ ⊤ :=
  LengthAlgebra.koszul_finite_of_homologySelf lam x hfin i

/-- パラメータ系の像は、長さ代数で用いるイデアルの根基を含む。 -/
lemma lengthAlgebra_ideal_le_radical
    {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    {e : ℕ} (z : Fin e → A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ z)) :
    (maximalIdeal D).map (algebraMap D C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
  have h := Ideal.map_radical_le (algebraMap D C)
    (I := Ideal.span (Set.range (algebraMap A D ∘ z)))
  rw [hsop.2, Ideal.map_span, ← Set.range_comp] at h
  simpa only [Function.comp_def, IsScalarTower.algebraMap_apply A D C] using h

/-- (2.4)、(2.6) を基底のパラメータで書き直すと、§4 の全ての正の冪の有限性が得られる。 -/
lemma normalized_koszul_pow_finite_of_lengthAlgebra
    {A D C : Type u} [CommRing A] [CommRing D] [IsLocalRing D]
    [Algebra A D] [CommRing C] [Algebra D C] [Algebra A C] [IsScalarTower A D C]
    {e : ℕ} (z : Fin e → A)
    (lam : NormalizedLength C ((maximalIdeal D).map (algebraMap D C)))
    (hzero : ∀ (x : Fin e → D), IsSystemOfParameters D x → ∀ v : ℕ, 0 < v →
      ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (x j ^ v)) i) = 0)
    (hbase : ∀ v : ℕ, 0 < v →
      lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (z j) ^ v))) =
        ((v ^ e * Module.finrank A D : ℕ) : ℝ≥0∞))
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ z))
    (v : ℕ) (hv : 0 < v) (i : ℤ) :
    lam.len ((koszulComplex (fun j ↦ (algebraMap A C (z j)) ^ v)).homology i) ≠ ⊤ := by
  obtain ⟨hzero', hquot⟩ := lengthAlgebra_base_values (C := C) hzero hbase hsop v hv
  have h := normalized_koszul_finite lam _ hzero'
    (by rw [hquot]; exact ENNReal.natCast_ne_top _) i
  have hx : (fun j ↦ algebraMap A C (z j ^ v)) =
      (fun j ↦ (algebraMap A C (z j)) ^ v) := funext fun j ↦ map_pow _ _ _
  rw [hx] at h
  exact h

end SerrePositivity.Section4
