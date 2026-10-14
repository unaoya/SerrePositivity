module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # 古典的冪商の逆系と差分写像

冪商の逆極限は既存のAdicCompletionに同定する。
これは普通の商加群の逆系についての計算であり、導来商や導来完備化との同値は主張しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity.DerivedCompletion
variable (R : Type*) [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-- イデアルの冪による商加群の逆系の各項。 -/
abbrev adicQuotientTower (n : ℕ) := M ⧸ (I ^ n • ⊤ : Submodule R M)

/-- 冪商の隣接する項の間の標準写像。 -/
def adicTowerTransition (n : ℕ) :
    adicQuotientTower R I M (n + 1) →ₗ[R] adicQuotientTower R I M n :=
  AdicCompletion.transitionMap I M (Nat.le_succ n)

/-- 冪商の遷移は全射。有限生成性・Noether性は不要。 -/
theorem adicTowerTransition_surjective (n : ℕ) :
    Function.Surjective (adicTowerTransition R I M n) :=
  Submodule.factor_surjective (Submodule.pow_smul_top_le I M (Nat.le_succ n))

/-- 普通の冪商の逆極限を、既存の古典的完備化へ同定する。 -/
def adicTowerLimitEquiv :
    moduleTowerLimit R (adicQuotientTower R I M) (adicTowerTransition R I M) ≃ₗ[R]
      AdicCompletion I M where
  toFun x := ⟨x.val, fun hmn ↦ (Submodule.eq_factor_of_eq_factor_succ
    (fun _ _ h ↦ Submodule.pow_smul_top_le I M h) x.val
    (fun n ↦ ((mem_moduleTowerLimit_iff R _ _ x.val).mp x.property n).symm) hmn).symm⟩
  invFun x := ⟨x.val, (mem_moduleTowerLimit_iff R _ _ _).mpr
    (fun n ↦ x.property (Nat.le_succ n))⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- 普通の冪商の直積上の差分写像は全射。 -/
theorem adicTowerDifference_surjective :
    Function.Surjective
      (moduleTowerDifference R (adicQuotientTower R I M) (adicTowerTransition R I M)) :=
  moduleTowerDifference_surjective R _ _ (adicTowerTransition_surjective R I M)

end SerrePositivity.DerivedCompletion
