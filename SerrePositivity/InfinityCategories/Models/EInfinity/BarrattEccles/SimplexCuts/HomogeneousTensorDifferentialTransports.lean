module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensorDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.GeneratorDifferentialValues

/-!
模型。文献の定義との比較は後で
# 同じテンソル微分の次数移送と零因子

Berger–Fresse §2.2.7、M14 L09の証明分割。
既存の斉次包含の添字移送と、微分が零の因子の成分を読む。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A]

/-- C263：同じ二因子の包含は、三つの次数の等式移送と可換。 -/
lemma tensorPair_cast_indices (P Q : Complex A) {i j k i' j' k' : ℤ}
    (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j') (hk : k = k')
    (x : P.X i) (y : Q.X j) :
    (eqToHom (congrArg (fun t : ℤ => (P ⊗ Q).X t) hk)).hom
        (ιTensorObj P Q i j k h (x ⊗ₜ[A] y)) =
      ιTensorObj P Q i' j' k' h'
        ((eqToHom (congrArg P.X hi)).hom x ⊗ₜ[A]
          (eqToHom (congrArg Q.X hj)).hom y) := by
  subst i'
  subst j'
  subst k'
  rfl

/-- C264：指定因子の微分が零なら、同じテンソル微分のその因子の成分は零。 -/
lemma tensorValueDifferentialFactor_eq_zero_of_closed (K : Complex A) (n : ℕ)
    (d : Fin n → ℕ) (v : ∀ i, K.X (-(d i : ℤ))) (i : Fin n)
    (h : K.d (-(d i : ℤ)) (-(d i : ℤ) + 1) (v i) = 0) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor K n d v i = 0 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    revert h
    refine Fin.cases ?_ (fun j => ?_) i
    · intro h
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor, Fin.cases_zero]
      rw [h, TensorProduct.zero_tmul, map_zero]
    · intro h
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValueDifferentialFactor, Fin.cases_succ]
      rw [ih (fun k => d k.succ) (fun k => v k.succ) j h,
        TensorProduct.tmul_zero, map_zero, smul_zero]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
