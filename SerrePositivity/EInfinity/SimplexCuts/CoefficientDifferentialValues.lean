module

public import SerrePositivity.EInfinity.SimplexCuts.RawAction
public import SerrePositivity.EInfinity.Surjection.DeletionDifferential

/-!
# 元の線形削除微分の同じ実基底での値

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のgeneratorとdifferentialを、同じrawComponentとcutSumで評価する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C284：元の生成元か零の評価を、同じcutSumか零として読む。 -/
lemma rawComponent_generator (S : SSet.{0}) {r d q : ℕ}
    (v : Fin ((r + 1) + d) → Fin (r + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q (Surjection.generator A v) (ModuleCat.freeMk (ULift.up x)) =
      if hv : Function.Surjective v ∧ Surjection.Nondegenerate v then
        cutSum A S (⟨v, hv⟩ : Surjection.BasisWord (r + 1) d) x
      else 0 := by
  by_cases hv : Function.Surjective v ∧ Surjection.Nondegenerate v
  · rw [dite_eq_left hv]
    have hg : Surjection.generator A v =
        Surjection.basis A (r + 1) d (ULift.up (⟨v, hv⟩ : Surjection.BasisWord (r + 1) d)) :=
      Surjection.generator_word A ⟨v, hv⟩
    rw [hg]
    exact rawComponent_value A S ⟨v, hv⟩ x
  · simp only [Surjection.generator, dite_eq_right hv, map_zero, LinearMap.zero_apply]

/-- C285：元の線形削除微分を、同じ実基底と生成元で評価する。 -/
lemma rawComponent_differential_basis (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌) :
    rawComponent A S r d q
        (Surjection.differential A (r + 1) d
          (Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
        (ModuleCat.freeMk (ULift.up x)) =
      ∑ i : Fin ((r + 1) + (d + 1)), Surjection.deletionCoefficient w.val i •
        rawComponent A S r d q (Surjection.generator A (Surjection.erase w.val i))
          (ModuleCat.freeMk (ULift.up x)) := by
  rw [Surjection.differential_basis]
  simp only [Surjection.differentialOnWord, map_sum, map_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]

end SerrePositivity.EInfinity.SimplexCuts
