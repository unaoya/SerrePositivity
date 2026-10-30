module

public import SerrePositivity.HomologicalAlgebra.Complex.Truncation

/-!
# 共通の次数幅による零ホモトピーの冪の制御

## 概要

射影複体のホモロジーを元 `r` が消すとき、`[a, a + w)` にある複体自身には
`r ^ w` が零ホモトピックに作用する。§4 の複体列では共通の幅 `w` を使うことで、
各段で独立に冪を選ぶことなく、一様な支持条件を得る。

## 証明と使い方

既存の `clear_degree` によって最上段から一段ずつ射を消す。
`exists_pow_nullHomotopy_of_homology_annihilated` の帰納法を、冪の存在ではなく
指定された幅を結論にする形で用いる。自由性・有限生成性・正則性は不要で、
各項の射影性と共通の次数範囲を仮定する。空の範囲も許す。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T]

/-- ホモロジーを消す元の、複体の次数幅乗は零ホモトピックに作用する。
最上段からの一段消去をちょうど `w` 回反復し、列に共通の冪を与える。 -/
theorem pow_width_nullHomotopy_of_homology_annihilated
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T) (a : ℤ) (w : ℕ)
    (hproj : ∀ i, Projective (P.X i))
    (hbound : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i))
    (hr : ∀ i, r • 𝟙 (P.homology i) = 0) :
    Nonempty (Homotopy (r ^ w • 𝟙 P) 0) := by
  have step : ∀ m : ℕ, ∃ f : P ⟶ P,
      (∀ i, a + w - m ≤ i → f.f i = 0) ∧
        (homotopyQuot T).map f = r ^ m • 𝟙 ((homotopyQuot T).obj P) := by
    intro m
    induction m with
    | zero =>
      refine ⟨𝟙 P, ?_, by simp⟩
      intro i hi
      exact (hbound i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ m ih =>
      obtain ⟨f, hf, hclass⟩ := ih
      have := hproj (a + w - m - 1)
      obtain ⟨g, hg, hgc⟩ := clear_degree P r (a + w - m - 1) f
        (fun i hi ↦ hf i (by omega)) (hr _)
      refine ⟨g, fun i hi ↦ hg i (by omega), ?_⟩
      rw [hgc, hclass, ← mul_smul, ← pow_succ']
  obtain ⟨f, hf, hc⟩ := step w
  have hzero : f = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i < a
    · exact (hbound i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  apply (nonempty_homotopy_smul_id_zero_iff _ P).mpr
  rw [← hc, hzero, Functor.map_zero]

/-- `r ^ N` が各ホモロジーを消すなら、幅 `w` の射影複体には `r ^ (N * w)` が
零ホモトピックに作用する。消去指数と次数幅を別々に制御するための形。 -/
theorem pow_mul_width_nullHomotopy_of_homology_annihilated
    (P : CochainComplex (ModuleCat.{u} T) ℤ) (r : T) (N : ℕ) (a : ℤ) (w : ℕ)
    (hproj : ∀ i, Projective (P.X i))
    (hbound : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i))
    (hr : ∀ i, r ^ N • 𝟙 (P.homology i) = 0) :
    Nonempty (Homotopy (r ^ (N * w) • 𝟙 P) 0) := by
  simpa only [pow_mul] using
    pow_width_nullHomotopy_of_homology_annihilated P (r ^ N) a w hproj hbound hr

/-- 共通の幅とホモロジーの消去指数をもつ射影複体の族は、共通の冪による
零ホモトピーをもつ。族の添字やパラメータの添字に冪を依存させない。 -/
theorem uniform_nullHomotopies_of_homology_annihilated {κ ι : Type*}
    (P : κ → CochainComplex (ModuleCat.{u} T) ℤ) (x : ι → T)
    (N : ℕ) (a : ℤ) (w : ℕ)
    (hproj : ∀ k i, Projective ((P k).X i))
    (hbound : ∀ k i, (i < a ∨ a + w ≤ i) → IsZero ((P k).X i))
    (hr : ∀ k j i, x j ^ N • 𝟙 ((P k).homology i) = 0) :
    ∀ k j, Nonempty (Homotopy (smulId (x j ^ (N * w)) (P k)) 0) := by
  intro k j
  exact pow_mul_width_nullHomotopy_of_homology_annihilated
    (P k) (x j) N a w (hproj k) (hbound k) (hr k j)

end SerrePositivity
