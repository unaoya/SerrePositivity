module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
模型。文献の定義との比較は後で
# 切断項の斉次純粋テンソル

Berger–Fresse §2.2.6 の切断項を任意の複体で読む。
L04 の証明の分割として、一因子が零なら純粋テンソルが零であることを示す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

def degreeSum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, d => d 0 + degreeSum n (fun i => d i.succ)

lemma degreeSum_eq_sum (n : ℕ) (d : Fin n → ℕ) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d = ∑ i, d i := by
  induction n with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum]
  | succ n ih => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Fin.sum_univ_succ, ih]

/-- 負自然数次数の元の右括弧純粋テンソル（BF §2.2.6）。 -/
def tensorValue (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (∀ i, K.X (-(d i : ℤ))) → (power K n).X (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ))
  | 0, _, _ => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  | n + 1, d, v =>
    ιTensorObj K (power K n) (-(d 0 : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun i => d i.succ) : ℤ))
      (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ)) (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add]; omega)
      (v 0 ⊗ₜ[A] tensorValue K n (fun i => d i.succ) (fun i => v i.succ))

/-- L04 の証明の分割：一つの零因子をテンソル包含へ運ぶ。 -/
lemma tensorValue_eq_zero (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (v : ∀ i, K.X (-(d i : ℤ))) → ∀ i, v i = 0 → _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v = 0
  | 0, _, _, i => Fin.elim0 i
  | n + 1, d, v, i => Fin.cases
      (fun h => by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue, h, TensorProduct.zero_tmul, map_zero]; rfl)
      (fun j h => by
        have ht := tensorValue_eq_zero K n (fun k => d k.succ) (fun k => v k.succ) j h
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue, ht, TensorProduct.tmul_zero, map_zero]; rfl) i

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
