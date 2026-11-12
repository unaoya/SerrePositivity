module

public import SerrePositivity.AlgebraicGeometry.ProjectiveGradedLocalizedDirectSum
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumRestriction

/-!
概要：斉次局所化の直和比較と、標準開を狭める制限との自然性。
方針：周囲の局所化の制限へ戻し、各成分の式で比較する。
規約：分母を広げる因子の冪が、分子の指定部分を対応させることを仮定する。
使われ方：Rees–Čech 比較の係数図式の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {R S κ : Type*} [CommRing R] [CommRing S] [Algebra R S] [DecidableEq κ]
variable {M : κ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
variable [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)]

/-- 斉次局所化の直和比較の各成分は、周囲の局所化の同じ成分。 -/
theorem projectiveGradedLocalizedDirectSumLinearEquiv_component_val
    (f : S) (V : ∀ i, ℕ → Submodule R (M i))
    (hstep : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1))
    (z : projectiveGradedAway f (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k))) (i : κ) :
    ((projectiveGradedLocalizedDirectSumLinearEquiv f V hstep z) i).val =
      (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M z.val) i := by
  exact congrArg (fun x ↦ x i) (projectiveGradedLocalizedDirectSumLinearEquiv_val f V hstep z)

/-- 追加因子が各分子を保つなら、直和の分子も保つ。 -/
theorem projectiveDirectSumSubmodule_restriction_mem (a : S)
    (V W : ∀ i, ℕ → Submodule R (M i))
    (h : ∀ (i : κ) (k : ℕ) (m : V i k), a ^ k • m.val ∈ W i k)
    (k : ℕ) (m : projectiveDirectSumSubmodule (fun i ↦ V i k)) :
    a ^ k • m.val ∈ projectiveDirectSumSubmodule (fun i ↦ W i k) := by
  rw [mem_projectiveDirectSumSubmodule]
  intro i
  exact h i k ⟨m.val i, (mem_projectiveDirectSumSubmodule _ _).mp m.property i⟩

/-- 斉次局所化の直和比較は、分母を広げる制限写像に自然。 -/
theorem projectiveGradedLocalizedDirectSumLinearEquiv_restriction
    {f g a : S} (ha : g = f * a) (V W : ∀ i, ℕ → Submodule R (M i))
    (hV : ∀ (i : κ) (k : ℕ) (m : V i k), f • m.val ∈ V i (k + 1))
    (hW : ∀ (i : κ) (k : ℕ) (m : W i k), g • m.val ∈ W i (k + 1))
    (h : ∀ (i : κ) (k : ℕ) (m : V i k), a ^ k • m.val ∈ W i k)
    (z : projectiveGradedAway f (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k))) :
    DirectSum.lmap (fun i ↦ projectiveGradedAwayRestriction ha (V i) (W i) (h i))
        (projectiveGradedLocalizedDirectSumLinearEquiv f V hV z) =
      projectiveGradedLocalizedDirectSumLinearEquiv g W hW
        (projectiveGradedAwayRestriction ha
          (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ V i k))
          (fun k ↦ projectiveDirectSumSubmodule (fun i ↦ W i k))
          (projectiveDirectSumSubmodule_restriction_mem a V W h) z) := by
  apply (DirectSum.lmap_injective
    (fun i ↦ (projectiveGradedAway g (W i)).subtype)).mpr (fun i ↦ Subtype.val_injective)
  apply DFinsupp.ext
  intro i
  change (projectiveGradedAwayRestriction ha (V i) (W i) (h i)
      ((projectiveGradedLocalizedDirectSumLinearEquiv f V hV z) i)).val = _
  rw [projectiveGradedAwayRestriction_val,
    projectiveGradedLocalizedDirectSumLinearEquiv_component_val]
  change projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
    ((projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M z.val) i) =
      ((projectiveGradedLocalizedDirectSumLinearEquiv g W hW _ ) i).val
  rw [projectiveGradedLocalizedDirectSumLinearEquiv_component_val,
    projectiveGradedAwayRestriction_val]
  exact (congrArg (fun x ↦ x i) (DFunLike.congr_fun
    (projectiveLocalizedDirectSumLinearEquiv_restriction (M := M)
      (show f ∣ g from ⟨a, ha⟩)) z.val)).symm

end SerrePositivity.AlgebraicGeometry
