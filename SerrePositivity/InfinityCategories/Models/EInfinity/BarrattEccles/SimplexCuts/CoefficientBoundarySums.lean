module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientWordComparisons
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HorizontalBoundaryValues

/-!
模型。文献の定義との比較は後で
# 同じ指定係数位置の境界和

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
元の線形削除の生成元と、同じ指定位置の切断の有限和を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C294：元の文字削除の生成元の評価は、同じpositiveWordの削除語のcutSumか零。 -/
lemma rawComponent_generator_erase_positiveWord (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1))
    (a : Fin ((r + 1) + (d + 1))) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.generator A (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a))
        (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
          (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) ∧
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) then
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S (Eq.mp (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1))
          (by omega : r + d + 1 = (r + 1) + d))
          ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
            (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a), hv⟩) x
      else 0 := by
  have hl : r + d + 1 = (r + 1) + d := by omega
  have he : (fun i : Fin ((r + 1) + d) => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
      (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a) (Fin.cast hl.symm i)) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a := by
    funext i
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a (Fin.cast hl (Fin.cast hl.symm i)) := by
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.erase_positiveWord]
      _ = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a i := congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase w.val a) (Fin.ext rfl)
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_generator_cast_length A S hl
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val
      (Fin.cast (by omega : (r + 1) + (d + 1) = r + d + 2) a)) x
  rw [he] at ht
  exact ht

/-- C295：同じ指定係数位置に属する全切断の和を、その削除語のcutSumへ戻す。 -/
lemma coefficientBoundaryTerm_sum_cut (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) (d + 1)) (a : Fin (r + d + 2)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r (d + 1) q w (a, s) x) =
      if hv : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a) ∧
          _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a) then
        -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.deletionCoefficient (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a •
          (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S (Eq.mp (congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Word (r + 1))
              (by omega : r + d + 1 = (r + 1) + d))
              ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a, hv⟩) x)
      else 0 := by
  have hs (s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q) := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm_succ_eq A S w (a, s) x
    (by omega : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) =
      -(((d + 1) + q : ℕ) : ℤ) + 1)
  simp_rw [hs]
  by_cases hv : Function.Surjective (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a) ∧
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.Nondegenerate (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.erase (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a)
  · simp only [dite_eq_left hv, ← Finset.smul_sum]
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord_of_cast]
    have step {M N P : ModuleCat A} (hMN : M = N) (hNP : N = P) (y : M) :
        (eqToHom hNP).hom ((eqToHom hMN).hom y) = (eqToHom (hMN.trans hNP)).hom y := by
      subst N
      subst P
      rfl
    rw [step]
    simp only [map_sum]
  · simp only [dite_eq_right hv, Finset.sum_const_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
