module

public import SerrePositivity.EInfinity.SimplexCuts.HomogeneousTensor

/-!
# 切断項の斉次純粋テンソルの自然性

Berger–Fresse §2.2.6。L05 の前提計算2として、複体射を純粋テンソルの各因子へ移す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] {K L : Complex A}

lemma tensorValue_map (f : K ⟶ L) (n : ℕ) (d : Fin n → ℕ)
    (v : ∀ i, K.X (-(d i : ℤ))) :
    (TensorPowers.map f n).f (-(degreeSum n d : ℤ)) (tensorValue K n d v) =
      tensorValue L n d (fun i => f.f (-(d i : ℤ)) (v i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := congrArg
      (fun z => z (v 0 ⊗ₜ[A] tensorValue K n (fun i => d i.succ) (fun i => v i.succ)))
      (ι_tensorHom f (TensorPowers.map f n) (-(d 0 : ℤ))
        (-(degreeSum n (fun i => d i.succ) : ℤ)) (-(degreeSum (n + 1) d : ℤ))
        (by simp only [degreeSum, Nat.cast_add]; omega))
    simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] at h
    exact h.trans (congrArg
      (fun z => ιTensorObj L (power L n) (-(d 0 : ℤ))
        (-(degreeSum n (fun i => d i.succ) : ℤ)) (-(degreeSum (n + 1) d : ℤ))
        (by simp only [degreeSum, Nat.cast_add]; omega) (f.f _ (v 0) ⊗ₜ[A] z))
      (ih (fun i => d i.succ) (fun i => v i.succ)))

end SerrePositivity.EInfinity.SimplexCuts
