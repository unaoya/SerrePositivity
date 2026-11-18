module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensor

/-!
模型。文献の定義との比較は後で
# 同じ純粋テンソルの一因子での有限和と整数倍

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の右括弧テンソルの一因子の線形性を、同じ次数の族で読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- C268：指定した一因子での有限和は、同じ純粋テンソルの有限和になる。 -/
lemma tensorValue_sum_factor {J : Type*} [Fintype J] (K : Complex A) (n : ℕ)
    (d : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ)))
    (w : J → ∀ i, K.X (-(d i : ℤ))) (a : Fin n)
    (hv : v a = ∑ j, w j a) (hw : ∀ j b, b ≠ a → w j b = v b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v = ∑ j, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d (w j) := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    revert hv hw
    refine Fin.cases ?_ (fun a => ?_) a
    · intro hv hw
      have ht : ∀ j, (fun i : Fin n => w j i.succ) = (fun i : Fin n => v i.succ) := by
        intro j
        funext i
        exact hw j i.succ (Fin.succ_ne_zero i)
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue, hv, TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [ht j]
    · intro hv hw
      have ht := ih (fun i => d i.succ) (fun i => v i.succ) (fun j i => w j i.succ) a hv
        (by intro j b hb; exact hw j b.succ (fun he => hb (Fin.succ_inj.mp he)))
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue]
      rw [ht, TensorProduct.tmul_sum, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hw j 0 (Fin.succ_ne_zero a).symm]

/-- C269：指定した一因子での整数倍は、同じ純粋テンソルの整数倍になる。 -/
lemma tensorValue_zsmul_factor (K : Complex A) (n : ℕ) (d : Fin n → ℕ)
    (v w : ∀ i, K.X (-(d i : ℤ))) (a : Fin n) (z : ℤ)
    (hv : v a = z • w a) (hw : ∀ b, b ≠ a → w b = v b) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v = z • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d w := by
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    revert hv hw
    refine Fin.cases ?_ (fun a => ?_) a
    · intro hv hw
      have ht : (fun i : Fin n => w i.succ) = (fun i : Fin n => v i.succ) := by
        funext i
        exact hw i.succ (Fin.succ_ne_zero i)
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue, hv, ← TensorProduct.smul_tmul', map_zsmul]
      rw [ht]
    · intro hv hw
      have ht := ih (fun i => d i.succ) (fun i => v i.succ) (fun i => w i.succ) a hv
        (by intro b hb; exact hw b.succ (fun he => hb (Fin.succ_inj.mp he)))
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue]
      rw [ht, TensorProduct.tmul_smul, map_zsmul, hw 0 (Fin.succ_ne_zero a).symm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
