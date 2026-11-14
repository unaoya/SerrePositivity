module

public import SerrePositivity.EInfinity.SimplexCuts.CoefficientWordComparisons
public import SerrePositivity.EInfinity.SimplexCuts.HorizontalBoundaryValues

/-!
# 同じ指定係数位置の境界和

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
元の線形削除の生成元と、同じ指定位置の切断の有限和を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C294：元の文字削除の生成元の評価は、同じpositiveWordの削除語のcutSumか零。 -/
lemma rawComponent_generator_erase_positiveWord (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1))
    (a : Fin ((r + 1) + (d + 1))) (x : S _⦋q⦌) :
    rawComponent A S r d q (Surjection.generator A (Surjection.erase w.val a))
        (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective (Surjection.erase (positiveWord w).val
          (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) then
        cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1))
          (by omega : r + d + 1 = (r + 1) + d))
          ⟨Surjection.erase (positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a), hv⟩) x
      else 0 := by
  have hl : r + d + 1 = (r + 1) + d := by omega
  have he : (fun i : Fin ((r + 1) + d) => Surjection.erase (positiveWord w).val
      (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) (Fin.cast hl.symm i)) =
      Surjection.erase w.val a := by
    funext i
    calc
      _ = Surjection.erase w.val a (Fin.cast hl (Fin.cast hl.symm i)) := by
        rw [erase_positiveWord]
      _ = Surjection.erase w.val a i := congrArg (Surjection.erase w.val a) (Fin.ext rfl)
  have ht := rawComponent_generator_cast_length A S hl
    (Surjection.erase (positiveWord w).val
      (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) x
  rw [he] at ht
  exact ht

/-- C295：同じ指定係数位置に属する全切断の和を、その削除語のcutSumへ戻す。 -/
lemma coefficientBoundaryTerm_sum_cut (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (a : Fin (r + d + 2)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ s : Cut (r + d) q, coefficientBoundaryTerm A S r (d + 1) q w (a, s) x) =
      if hv : Function.Surjective (Surjection.erase (positiveWord w).val a) ∧
          Surjection.Nondegenerate (Surjection.erase (positiveWord w).val a) then
        -Surjection.deletionCoefficient (positiveWord w).val a •
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (cutSum A S (Eq.mp (congrArg (Surjection.Word (r + 1))
              (by omega : r + d + 1 = (r + 1) + d))
              ⟨Surjection.erase (positiveWord w).val a, hv⟩) x)
      else 0 := by
  have hs (s : Cut (r + d) q) := coefficientBoundaryTerm_succ_eq A S w (a, s) x
    (by omega : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
      -(((d + 1) + q : ℕ) : ℤ) + 1)
  simp_rw [hs]
  by_cases hv : Function.Surjective (Surjection.erase (positiveWord w).val a) ∧
      Surjection.Nondegenerate (Surjection.erase (positiveWord w).val a)
  · simp only [dite_eq_left hv, ← Finset.smul_sum]
    unfold cutSum
    rw [positiveWord_of_cast]
    have step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
        (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
      subst N
      subst P
      rfl
    rw [step]
    simp only [map_sum]
  · simp only [dite_eq_right hv, Finset.sum_const_zero]

end SerrePositivity.EInfinity.SimplexCuts
