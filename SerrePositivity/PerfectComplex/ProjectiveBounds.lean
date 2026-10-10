module

public import SerrePositivity.PerfectComplex.KoszulLengthBounds
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Basic.ENNReal.BigOperators

/-! # 有限射影項をもつ複体の Koszul 長さの有限性

基底の代わりに有限自由加群の直和因子表示を使う。基礎環の局所性・
ネーター性・有限代数性・平坦性は仮定しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal BigOperators

variable {C : Type u} [CommRing C]

/-- 有限射影加群は有限自由加群の直和因子である。 -/
lemma finiteProjective_exists_retract (M : ModuleCat.{u} C)
    [Module.Finite C M] [Module.Projective C M] :
    ∃ n : ℕ, Nonempty (Retract M (ModuleCat.of C (Fin n → C))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' C M
  obtain ⟨g, hg⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  exact ⟨n, ⟨⟨ModuleCat.ofHom g, ModuleCat.ofHom f, ModuleCat.hom_ext hg⟩⟩⟩

variable {J : Ideal C} (lam : NormalizedLength C J)

/-- 有限射影項の有界複体に対する Koszul ホモロジーの有限性。 -/
lemma lambdaHomology_koszul_projective_ne_top (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ q : ℤ, lam.len ((koszulComplex x).homology q) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfinite : ∀ q, Module.Finite C (P.X q))
    (hproj : ∀ q, Module.Projective C (P.X q))
    (hbound : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q)) (q : ℤ) :
    lam.len ((koszulComplexOn x P).homology q) ≠ ⊤ := by
  classical
  have hterm (i : ℤ) : ∃ r : ℕ, Nonempty (Retract (P.X i) (ModuleCat.of C (Fin r → C))) := by
    have := hfinite i
    have := hproj i
    exact finiteProjective_exists_retract _
  choose r hr using hterm
  obtain ⟨a, b, hab⟩ := hbound
  have hle := lambdaHomology_koszulComplexOn_le_sum_of_retracts lam hfg x hJ
    a (b + 1 - a).toNat r P (fun i hi ↦ hab i (by omega)) (fun i _ _ ↦ hr i) q
  apply ne_top_of_le_ne_top _ hle
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (hfin _)

/-- Koszul 有限性と台から、有限射影複体の全ホモロジーの長さが有限となる。 -/
theorem lambdaHomology_supported_projective_ne_top (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (hfin : ∀ v : ℕ, 0 < v → ∀ q : ℤ,
      lam.len ((koszulComplex (fun j ↦ x j ^ v)).homology q) ≠ ⊤)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hfinite : ∀ q, Module.Finite C (P.X q))
    (hproj : ∀ q, Module.Projective C (P.X q))
    (hbound : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (hsupp : IsSupported x P) (q : ℤ) : lam.len (P.homology q) ≠ ⊤ := by
  obtain ⟨v, hv, hnull⟩ := hsupp.exists_pos
  exact lambdaHomology_ne_top_of_koszulComplexOn lam hfg (fun j ↦ x j ^ v)
    (le_radical_span_pow x hJ v) P hnull q
    (lambdaHomology_koszul_projective_ne_top lam hfg (fun j ↦ x j ^ v)
      (le_radical_span_pow x hJ v) (hfin v hv) P hfinite hproj hbound q)

end SerrePositivity
