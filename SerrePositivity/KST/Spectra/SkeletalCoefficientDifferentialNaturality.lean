module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientNaturality
public import SerrePositivity.KST.Spectra.SkeletalCoefficientDifferential

/-!
概要：セルの高次係数に移した幾何的微分の係数自然性。
方針：fiber の群同型の逆の自然性と実際の塔の微分の自然性を共役する。
規約：誘導準同型は各非退化単体に座標ごとに作用する。
使われ方：Goerss–Jardine VIII §1。通常の cochain 微分との比較の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：実際の tower 微分を移した係数微分は点つき係数射に自然。
方針：始域の群同型の逆を自然性で移し、微分と終域の群同型の自然性を適用する。
規約：係数の二つの次数表記はそれぞれの fiber の群の表示に合わせる。
使われ方：Goerss–Jardine VIII §1。幾何的な有理 cochain の自然な構成。 -/
theorem coefficientDifferential_natural (K : SSet.{u}) {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n r : ℕ)
    (a : coefficientGroup K Y n (r + 1)) :
    coefficientDifferential K Z n r (fun s ↦ pointedGroupMap (n + 1 + (r + 1)) p (a s)) =
      fun s ↦ pointedGroupMap (n + 1 + 1 + r) p (coefficientDifferential K Y n r a s) := by
  let b := (stageFiberCoefficientEquiv K Y n (r + 1)).symm a
  have hInv : (stageFiberCoefficientEquiv K Z n (r + 1)).symm
      (fun s ↦ pointedGroupMap (n + 1 + (r + 1)) p (a s)) =
      pointedGroupMap (X := UnbasedPointedMapping.stageFiber K Y n)
        (Y := UnbasedPointedMapping.stageFiber K Z n) (r + 1)
        (UnbasedPointedMapping.stageFiberMap K (Y := Y) (Z := Z) p n) b := by
    apply (stageFiberCoefficientEquiv K Z n (r + 1)).injective
    rw [MulEquiv.apply_symm_apply, stageFiberCoefficientEquiv_natural]
    simp only [b, MulEquiv.apply_symm_apply]
  rw [coefficientDifferential_apply, coefficientDifferential_apply, hInv,
    ← UnbasedPointedMapping.stageDifferential_natural K p n r b,
    stageFiberCoefficientEquiv_natural]

end

end SerrePositivity.KST.Spectra.SkeletalCellAttachment
