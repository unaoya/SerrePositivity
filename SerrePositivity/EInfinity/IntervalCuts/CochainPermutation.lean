module

public import SerrePositivity.EInfinity.IntervalCuts.InputPermutation

/-!
# 区間余演算の整数複体射の対称群等変性

概要：Berger–Fresse §2.2.6 の色の置換を実際の複体射の等変性へまとめる。
方針：非零入力次数での双線形等式を全整数へ移し、斉次テンソルの外延性を適用する。
規約：正次数の χ と区間の零・−1 以外の入力を零対象で処理する。
使われ方：χ-coalgebra の equivariance フィールド。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：全整数の双線形区間余演算は置換に対して等変（BF §2.2.6）。
方針：非正語次数と区間の二入力次数で自然数成分の置換等式を使う。
規約：和の任意の次数証明と任意の二入力元。
使われ方：複体射の等変性を純粋テンソルで証明する。 -/
lemma cochainActionBilinear_permutation (n : ℕ) (σ : Equiv.Perm (Fin n))
    (r s t : ℤ) (h : r + s = t) (x : (complex A n).X r) (y : (interval A).X s) :
    cochainActionBilinear A n r s t h ((complexRename A n σ).f r x) y =
      (permutationAction (interval A) n σ).asIso.hom.f t
        (cochainActionBilinear A n r s t h x y) := by
  by_cases hr : 0 < r
  · rw [complex_eq_zero_of_positive A n r hr x]
    simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
  by_cases hs : s = 0
  · subst s
    have ht : t = -(d : ℤ) := by omega
    cases ht
    simp only [cochainActionBilinear_neg_vertex, complexRename_neg_hom_apply]
    exact congrArg (fun f : (interval A).X 0 →ₗ[A] (power (interval A) n).X (-(d : ℤ)) => f y)
      (vertexInputBilinear_permutation A n d σ ((complexXIso A n d).hom x))
  by_cases hs1 : s = -1
  · subst s
    have ht : t = -((d + 1 : ℕ) : ℤ) := by omega
    cases ht
    simp only [cochainActionBilinear_neg_edge, complexRename_neg_hom_apply]
    exact congrArg (fun f : (interval A).X (-1) →ₗ[A]
      (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f y)
      (edgeInputBilinear_permutation A n d σ ((complexXIso A n d).hom x))
  · rw [interval_eq_zero_of_other A s hs hs1 y]
    simp only [map_zero]

/-- 概要：実際の区間余演算の整数複体射は任意の色置換に対して等変（BF §2.2.6）。
方針：全整数テンソル成分と純粋テンソルで双線形等変性を適用する。
規約：語の左作用は出力の同じ Koszul 置換へ移る。
使われ方：χ の区間余代数の equivariance フィールドの具体的証明。 -/
lemma cochainAction_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (complexRename A n σ ▷ interval A) ≫ cochainAction A n =
      cochainAction A n ≫ (permutationAction (interval A) n σ).asIso.hom := by
  apply tensorHom_ext
  intro r s t h
  simp only [HomologicalComplex.comp_f, ι_whiskerRight_assoc,
    ι_cochainAction_assoc, ι_cochainAction]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact cochainActionBilinear_permutation A n σ r s t h x y

/-- 概要：χ の対称列の置換に対する区間余演算の等変性（BF §2.2.6）。
方針：対称列の置換成分を整数の色置換射へ同定する。
規約：有限全単射圏上の対称列と同じ規約。
使われ方：Operad.Coalgebra の equivariance フィールドへそのまま渡す。 -/
lemma cochainAction_equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((sequence A).map (FiniteBijection.permutation n σ) ▷ interval A) ≫ cochainAction A n =
      cochainAction A n ≫ (permutationAction (interval A) n σ).asIso.hom := by
  rw [sequence_map_permutation]
  exact cochainAction_permutation A n σ

end SerrePositivity.EInfinity.IntervalCuts
