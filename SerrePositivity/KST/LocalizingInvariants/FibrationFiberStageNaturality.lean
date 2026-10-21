module

public import SerrePositivity.KST.LocalizingInvariants.FibrationFiberPointedStage

/-!
概要：BF fiber の整数 π の点つき段表示は厳密な fibration 正方形に自然。
方針：元の BF 射の段表示の自然性と、持ち上げに保存した各段の比較式を使う。
規約：標準基点を保つ元の点つき fiber 比較に一致。使われ方：整数次数の接続射の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)
local instance naturalityPFibration (n : ℕ) : Fibration (p.app n).right := hp n
local instance naturalityQFibration (n : ℕ) : Fibration (q.app n).right := hq n

lemma pointedStageEquiv_natural (j : ℤ) (k n : ℕ) (hk : -j ≤ (k : ℤ))
    (hd : degree j k = n + 1) (x : homotopyGroup (fiber p hp) j) :
    pointedStageEquiv q j k n hk hd (homotopyMap (map p q a b h) j x) =
      pointedGroupMap n (level p q a b h k) (pointedStageEquiv p j k n hk hd x) := by
  simp only [pointedStageEquiv, MulEquiv.trans_apply, projectionPointedEquiv_apply,
    positiveStageEquiv_natural]
  change pointedGroupMap n (fiberLevelProjection q hq k)
    (pointedGroupMap n ((map p q a b h).app k)
      (positiveStageEquiv (fiber p hp) j k n hk hd x)) =
    pointedGroupMap n (level p q a b h k)
      (pointedGroupMap n (fiberLevelProjection p hp k)
        (positiveStageEquiv (fiber p hp) j k n hk hd x))
  rw [← pointedGroupMap_comp, ← pointedGroupMap_comp, map_level]

end SerrePositivity.KST.LocalizingInvariants.FibrationFiberComparison
