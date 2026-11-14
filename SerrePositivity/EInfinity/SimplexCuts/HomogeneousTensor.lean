module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation

/-!
# 切断項の斉次純粋テンソル

Berger–Fresse §2.2.6 の切断項を任意の複体で読む。
L04 の証明の分割として、一因子が零なら純粋テンソルが零であることを示す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

def degreeSum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, d => d 0 + degreeSum n (fun i => d i.succ)

lemma degreeSum_eq_sum (n : ℕ) (d : Fin n → ℕ) : degreeSum n d = ∑ i, d i := by
  induction n with
  | zero => simp [degreeSum]
  | succ n ih => simp only [degreeSum, Fin.sum_univ_succ, ih]

/-- 負自然数次数の元の右括弧純粋テンソル（BF §2.2.6）。 -/
def tensorValue (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (∀ i, K.X (-(d i : ℤ))) → (power K n).X (-(degreeSum n d : ℤ))
  | 0, _, _ => (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)
  | n + 1, d, v =>
    ιTensorObj K (power K n) (-(d 0 : ℤ)) (-(degreeSum n (fun i => d i.succ) : ℤ))
      (-(degreeSum (n + 1) d : ℤ)) (by simp only [degreeSum, Nat.cast_add]; omega)
      (v 0 ⊗ₜ[A] tensorValue K n (fun i => d i.succ) (fun i => v i.succ))

/-- L04 の証明の分割：一つの零因子をテンソル包含へ運ぶ。 -/
lemma tensorValue_eq_zero (K : Complex A) : (n : ℕ) → (d : Fin n → ℕ) →
    (v : ∀ i, K.X (-(d i : ℤ))) → ∀ i, v i = 0 → tensorValue K n d v = 0
  | 0, _, _, i => Fin.elim0 i
  | n + 1, d, v, i => Fin.cases
      (fun h => by simp only [tensorValue, h, TensorProduct.zero_tmul, map_zero]; rfl)
      (fun j h => by
        have ht := tensorValue_eq_zero K n (fun k => d k.succ) (fun k => v k.succ) j h
        simp only [tensorValue, ht, TensorProduct.tmul_zero, map_zero]; rfl) i

end SerrePositivity.EInfinity.SimplexCuts
