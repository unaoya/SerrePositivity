module

public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedDirectSumComponents
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechGradedRestriction

/-!
概要：局所化と直和の交換は、標準開を狭める制限写像と可換。
方針：分数の分子と分母を追加因子の冪で広げ、各成分で計算する。
規約：分母の任意の整除関係を許す。
使われ方：斉次局所化の直和同値を Čech の係数図式の同型へまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped DirectSum
attribute [local instance] LocalizedModule.moduleOfIsLocalization

variable {S κ : Type*} [CommRing S] [DecidableEq κ]
variable {M : κ → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module S (M i)]

/-- 局所化と直和の比較は、分母を広げる制限に自然。 -/
theorem projectiveLocalizedDirectSumLinearEquiv_restriction {f g : S} (h : f ∣ g) :
    (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers g) M).toLinearMap.comp
        (projectiveModuleAwayRestriction (M := ⨁ i, M i) h) =
      (DirectSum.lmap (fun i ↦ projectiveModuleAwayRestriction (M := M i) h)).comp
        (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M).toLinearMap := by
  obtain ⟨a, ha⟩ := h
  apply LinearMap.ext
  intro z
  induction z using LocalizedModule.induction_on with
  | _ m s =>
    obtain ⟨s, k, rfl⟩ := s
    apply DFinsupp.ext
    intro i
    change (projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers g) M
      (projectiveModuleAwayRestriction (show f ∣ g from ⟨a, ha⟩)
        (LocalizedModule.mk m (projDenominator f k)))) i =
      projectiveModuleAwayRestriction (M := M i) (show f ∣ g from ⟨a, ha⟩)
        ((projectiveLocalizedDirectSumLinearEquiv (Submonoid.powers f) M
          (LocalizedModule.mk m (projDenominator f k))) i)
    rw [projectiveModuleAwayRestriction_mk ha,
      projectiveLocalizedDirectSumLinearEquiv_mk_component,
      projectiveLocalizedDirectSumLinearEquiv_mk_component,
      projectiveModuleAwayRestriction_mk ha]
    rfl

end SerrePositivity.AlgebraicGeometry
