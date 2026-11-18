module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.HomogeneousTensor

/-!
模型。文献の定義との比較は後で
# 切断項の斉次純粋テンソルの自然性

Berger–Fresse §2.2.6。L05 の前提計算2として、複体射を純粋テンソルの各因子へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] {K L : Complex A}

lemma tensorValue_map (f : K ⟶ L) (n : ℕ) (d : Fin n → ℕ)
    (v : ∀ i, K.X (-(d i : ℤ))) :
    (_root_.SerrePositivity.TensorPowers.map f n).f (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n d : ℤ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n d v) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue L n d (fun i => f.f (-(d i : ℤ)) (v i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := congrArg
      (fun z => z (v 0 ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.tensorValue K n (fun i => d i.succ) (fun i => v i.succ)))
      (ι_tensorHom f (_root_.SerrePositivity.TensorPowers.map f n) (-(d 0 : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun i => d i.succ) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ))
        (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add]; omega))
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at h
    exact h.trans (congrArg
      (fun z => ιTensorObj L (power L n) (-(d 0 : ℤ))
        (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum n (fun i => d i.succ) : ℤ)) (-(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum (n + 1) d : ℤ))
        (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.degreeSum, Nat.cast_add]; omega) (f.f _ (v 0) ⊗ₜ[A] z))
      (ih (fun i => d i.succ) (fun i => v i.succ)))

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
