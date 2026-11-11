module

public import SerrePositivity.KST.Spectra.SkeletalDoubleLoopDifferential

/-!
概要：群の係数微分の基本段と通常の正規化交代微分の同定。
方針：二重 loop の係数同型で任意の入力を戻し、自然性と逆元による符号を整理する。
規約：骨格添字は一以上、cochain 次数は二以上。
使われ方：Goerss–Jardine VIII §1。係数複体の像と符号の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxRecDepth 2048 in
-- 二重 loop の係数同型と係数微分の入力の別名を照合するため。
/-- 実際の群の係数微分の基本段は、指定した符号を掛けた正規化交代微分。 -/
theorem coefficientDifferential_zero_alternating (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : coefficientGroup K Y (n + 1) 1) (s : K.nonDegenerate (n + 3)) :
    Additive.ofMul (coefficientDifferential K Y (n + 1) 0 a s) =
      (-1 : ℤ) ^ (n + 4) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint)))
        (n + 2) (fun t ↦ Additive.ofMul (a t)) s := by
  let e := doubleLoopCoefficientEquiv Y n
  let c := fun t ↦ e.symm ((a t)⁻¹)
  have hi : (fun t ↦ (e (c t))⁻¹) = a := by
    funext t
    simp only [c, e.apply_symm_apply, inv_inv]
  have ha : (fun t ↦ e.toAdditive (Additive.ofMul (c t))) =
      (fun t ↦ -Additive.ofMul (a t)) := by
    funext t
    change Additive.ofMul (e (e.symm ((a t)⁻¹))) = _
    rw [e.apply_symm_apply]
    rfl
  have h := doubleLoop_normalizedDifferential K Y n c s
  have hm := NormalizedValueCochains.differential_map K
    (M := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right
      (n + 1) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint)))
    (N := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint)))
    e.toAdditive.toAddMonoidHom
    (n + 2) (fun t ↦ Additive.ofMul (c t)) s
  have hl : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint)))
      (n + 2) (fun t ↦ e.toAdditive (Additive.ofMul (c t))) s =
      -_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint)))
        (n + 2) (fun t ↦ Additive.ofMul (a t)) s := by
    rw [ha]
    change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint))) (n + 2)
      (-(fun t ↦ Additive.ofMul (a t)))) s = _
    rw [map_neg]
    rfl
  have hh := hl.symm.trans (hm.trans h)
  rw [hi] at hh
  rcases neg_one_pow_eq_or ℤ (n + 3) with hs | hs
  · rw [hs, one_zsmul] at hh
    simpa only [show n + 4 = (n + 3) + 1 from rfl, pow_succ, hs, one_mul,
      neg_one_zsmul] using hh.symm
  · rw [hs, neg_one_zsmul] at hh
    simpa only [show n + 4 = (n + 3) + 1 from rfl, pow_succ, hs, neg_mul_neg,
      one_mul, one_zsmul] using (neg_injective hh).symm

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
