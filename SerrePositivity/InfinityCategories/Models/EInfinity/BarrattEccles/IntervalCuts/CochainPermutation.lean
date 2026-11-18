module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.InputPermutation

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：全整数の双線形区間余演算は置換に対して等変（BF §2.2.6）。
方針：非正語次数と区間の二入力次数で自然数成分の置換等式を使う。
規約：和の任意の次数証明と任意の二入力元。
使われ方：複体射の等変性を純粋テンソルで証明する。 -/
lemma cochainActionBilinear_permutation (n : ℕ) (σ : Equiv.Perm (Fin n))
    (r s t : ℤ) (h : r + s = t) (x : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A n).X r) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X s) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ).f r x) y =
      (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n σ).asIso.hom.f t
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear A n r s t h x y) := by
  by_cases hr : 0 < r
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex_eq_zero_of_positive A n r hr x]
    simp only [map_zero, LinearMap.zero_apply]
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, r = -(d : ℤ) := ⟨(-r).toNat, by omega⟩
  by_cases hs : s = 0
  · subst s
    have ht : t = -(d : ℤ) := by omega
    cases ht
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_vertex, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.complexRename_neg_hom_apply]
    exact congrArg (fun f : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X 0 →ₗ[A] (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-(d : ℤ)) => f y)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.vertexInputBilinear_permutation A n d σ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x))
  by_cases hs1 : s = -1
  · subst s
    have ht : t = -((d + 1 : ℕ) : ℤ) := by omega
    cases ht
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_neg_edge, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.complexRename_neg_hom_apply]
    exact congrArg (fun f : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A).X (-1) →ₗ[A]
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f y)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.edgeInputBilinear_permutation A n d σ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A n d).hom x))
  · rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval_eq_zero_of_other A s hs hs1 y]
    simp only [map_zero]

/-- 概要：実際の区間余演算の整数複体射は任意の色置換に対して等変（BF §2.2.6）。
方針：全整数テンソル成分と純粋テンソルで双線形等変性を適用する。
規約：語の左作用は出力の同じ Koszul 置換へ移る。
使われ方：χ の区間余代数の equivariance フィールドの具体的証明。 -/
lemma cochainAction_permutation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexRename A n σ ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n ≫ (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n σ).asIso.hom := by
  apply tensorHom_ext
  intro r s t h
  simp only [HomologicalComplex.comp_f, ι_whiskerRight_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ι_cochainAction_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.ι_cochainAction]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainActionBilinear_permutation A n σ r s t h x y

/-- 概要：χ の対称列の置換に対する区間余演算の等変性（BF §2.2.6）。
方針：対称列の置換成分を整数の色置換射へ同定する。
規約：有限全単射圏上の対称列と同じ規約。
使われ方：Operad.Coalgebra の equivariance フィールドへそのまま渡す。 -/
lemma cochainAction_equivariance (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence A).map (_root_.SerrePositivity.FiniteBijection.permutation n σ) ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction A n ≫ (permutationAction (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.interval A) n σ).asIso.hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.sequence_map_permutation]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts.cochainAction_permutation A n σ

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.IntervalCuts
