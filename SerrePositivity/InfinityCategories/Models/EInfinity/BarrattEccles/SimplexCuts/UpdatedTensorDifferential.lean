module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensorHEq

/-!
模型。文献の定義との比較は後で
# 一因子の微分と同じ更新次数の純粋テンソル

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存のKoszul微分の成分を、同じ因子の値と次数の等式で照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- C272：同じ一因子の微分は、更新した同じ次数のテンソルに接頭次数の符号を掛けたもの。 -/
lemma tensorValueDifferentialFactor_eq_updated_tensor (K : Complex A) (n : ℕ)
    (d e : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ)))
    (w : ∀ i, K.X (-(e i : ℤ))) (a : Fin n)
    (hd : ∀ b, d b = e b + if b = a then 1 else 0)
    (hv : HEq (K.d (-(d a : ℤ)) (-(d a : ℤ) + 1) (v a)) (w a))
    (hw : ∀ b, b ≠ a → HEq (v b) (w b))
    (h : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n e : ℤ) = -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ) + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor K n d v a =
      (-1 : ℤ) ^ (∑ b ∈ Finset.univ.filter (fun b : Fin n => b < a), d b) •
        (eqToHom (congrArg (fun z : ℤ => (power K n).X z) h)).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n e w) := by
  have hcast {M N : ModuleCat A} (hMN : M = N) (y : M) :
      HEq ((eqToHom hMN).hom y) y := by subst N; rfl
  induction n with
  | zero => exact Fin.elim0 a
  | succ n ih =>
    revert hd hv hw h
    refine Fin.cases ?_ (fun a => ?_) a
    · intro hd hv hw h
      have he : (fun b : Fin n => d b.succ) = (fun b => e b.succ) := by
        funext b
        simpa only [Fin.succ_ne_zero, ite_false, Nat.add_zero] using hd b.succ
      have htail := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue_heq_degree K n _ _ he _ _
        (fun b => hw b.succ (Fin.succ_ne_zero b))
      have hzero : d 0 = e 0 + 1 := by simpa only [ite_true] using hd 0
      have hp : (∑ b ∈ Finset.univ.filter (fun b : Fin (n + 1) => b < 0), d b) = 0 := by
        simp
      rw [hp, pow_zero, one_smul]
      apply eq_of_heq
      refine HEq.trans ?_ (hcast (congrArg (fun z : ℤ => (power K (n + 1)).X z) h)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K (n + 1) e w)).symm
      dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor, Fin.cases_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue]
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorPair_heq_indices K (power K n)
      · omega
      · rw [he]
      · exact h.symm
      · exact hv
      · exact htail
    · intro hd hv hw h
      have hzero : d 0 = e 0 := by
        simpa only [(Fin.succ_ne_zero a).symm, ite_false, Nat.add_zero] using hd 0
      have htail : -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun b => e b.succ) : ℤ) =
          -(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun b => d b.succ) : ℤ) + 1 := by
        simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add] at h
        omega
      have hdt : ∀ b : Fin n, d b.succ = e b.succ + if b = a then 1 else 0 := by
        intro b
        simpa only [Fin.succ_inj] using hd b.succ
      have ht := ih (fun b => d b.succ) (fun b => e b.succ)
        (fun b => v b.succ) (fun b => w b.succ) a hdt hv
        (fun b hb => hw b.succ (fun he => hb (Fin.succ_inj.mp he))) htail
      have hp : (∑ b ∈ Finset.univ.filter (fun b : Fin (n + 1) => b < a.succ), d b) =
          d 0 + ∑ b ∈ Finset.univ.filter (fun b : Fin n => b < a), d b.succ := by
        simp [Finset.sum_filter, Fin.sum_univ_succ]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor, Fin.cases_succ]
      rw [ht, hp]
      simp only [TensorProduct.tmul_smul, map_zsmul, Units.smul_def,
        Int.negOnePow_neg, Int.coe_negOnePow_natCast, ← mul_smul, ← pow_add]
      congr 1
      apply eq_of_heq
      refine HEq.trans ?_ (hcast (congrArg (fun z : ℤ => (power K (n + 1)).X z) h)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K (n + 1) e w)).symm
      dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue]
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorPair_heq_indices K (power K n)
      · omega
      · exact htail.symm
      · exact h.symm
      · exact hw 0 (Fin.succ_ne_zero a).symm
      · exact hcast (congrArg (fun z : ℤ => (power K n).X z) htail)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n (fun b => e b.succ) (fun b => w b.succ))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
