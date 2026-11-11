module

public import SerrePositivity.KST.Spectra.SkeletalEdgeDoubleLoop
public import SerrePositivity.KST.Spectra.SkeletalCoefficientAlternating

/-!
概要：次数一を含む全ての正次数 cochain の実際の係数微分の交代式。
方針：二つの基本段を統合し、loop の反可換式で任意の高次数へ帰納する。
規約：添字の標準同定を明示し、値と符号を比較する。
使われ方：Goerss–Jardine VIII §1。骨格の係数微分の通常の正規化複体との同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 全ての正次数 cochain についての群の係数微分の基本段。 -/
theorem coefficientDifferential_zero_all_alternating (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (a : coefficientGroup K Y n 1) (s : K.nonDegenerate (n + 2)) :
    Additive.ofMul (coefficientDifferential K Y n 0 a s) =
      (-1 : ℤ) ^ (n + 3) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2) Y.basepoint)))
        (n + 1) (fun t ↦ Additive.ofMul (a t)) s := by
  cases n with
  | zero => simpa using first_coefficientDifferential_zero_alternating K Y a s
  | succ n => exact coefficientDifferential_zero_alternating K Y n a s

set_option maxRecDepth 2048 in
-- loop の係数同型と係数微分の入力の別名を照合するため。
/-- 群の係数微分の交代式。出力と入力の算術的に等しい次数を異種等式で保持する。 -/
theorem coefficientDifferential_all_alternating_heq (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : coefficientGroup K Y n (r + 1)) (s : K.nonDegenerate (n + 2)) :
    HEq (Additive.ofMul (coefficientDifferential K Y n r a s))
      ((-1 : ℤ) ^ (n + 3 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + (r + 1)) Y.basepoint)))
        (n + 1) (fun t ↦ Additive.ofMul (a t)) s) := by
  induction r generalizing Y with
  | zero => exact heq_of_eq (coefficientDifferential_zero_all_alternating K Y n a s)
  | succ r ih =>
    let e := loopPositiveHomotopyEquiv Y (n + 1 + (r + 1))
    let c := fun t ↦ e.symm (a t)
    have hi : (fun t ↦ e (c t)) = a := by
      funext t
      exact e.apply_symm_apply _
    have hd := coefficientDifferential_loopPositive K Y n r c s
    have hc := ih (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) c
    have hh := loopPositive_neg_heq Y
      (by omega : n + 1 + 1 + r = n + 1 + (r + 1)) _ _ hc
    have hm := NormalizedValueCochains.differential_map K
      (M := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right
        (n + 1 + (r + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
      (N := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
        (n + 1 + (r + 1) + 1) Y.basepoint)))
      e.toAdditive.toAddMonoidHom (n + 1) (fun t ↦ Additive.ofMul (c t)) s
    rw [hi] at hd
    have hd' : Additive.ofMul (coefficientDifferential K Y n (r + 1) a s) =
        -(loopPositiveHomotopyEquiv Y (n + 1 + 1 + r)).toAdditive
          (Additive.ofMul (coefficientDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n r c s)) :=
      congrArg Additive.ofMul hd
    apply (heq_of_eq hd').trans
    apply hh.trans
    apply heq_of_eq
    change -e.toAdditive _ = _
    rw [map_zsmul]
    have hmc := congrArg
      (fun z : Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + (r + 1) + 1) Y.basepoint) ↦
        -((-1 : ℤ) ^ (n + 3 + r) • z)) hm.symm
    apply hmc.trans
    have hia : (fun t ↦ e.toAdditive.toAddMonoidHom (Additive.ofMul (c t))) =
        (fun t ↦ Additive.ofMul (a t)) := by
      funext t
      exact congrArg Additive.ofMul (e.apply_symm_apply (a t))
    have hfinal := congrArg
      (fun q : K.nonDegenerate (n + 1) →
        Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + (r + 1) + 1) Y.basepoint) ↦
        -((-1 : ℤ) ^ (n + 3 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
            (n + 1 + (r + 1) + 1) Y.basepoint))) (n + 1) q s)) hia
    apply hfinal.trans
    have hsign : -((-1 : ℤ) ^ (n + 3 + r)) = (-1 : ℤ) ^ (n + 3 + (r + 1)) := by
      simpa only [mul_neg_one, Nat.add_assoc] using (pow_succ (-1 : ℤ) (n + 3 + r)).symm
    exact (neg_smul ((-1 : ℤ) ^ (n + 3 + r)) _).symm.trans
      (congrArg (fun z : ℤ ↦ z • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
          (n + 1 + (r + 1) + 1) Y.basepoint)))
        (n + 1) (fun t ↦ Additive.ofMul (a t)) s) hsign)

/-- 次数の標準同定の後、全ての正次数 cochain の係数微分は通常の交代微分の符号倍。 -/
theorem coefficientDifferential_all_alternating (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : coefficientGroup K Y n (r + 1)) (s : K.nonDegenerate (n + 2)) :
    (coefficientIndexEquiv Y
      (by omega : n + 1 + 1 + r = n + 1 + (r + 1))).toAdditive
        (Additive.ofMul (coefficientDifferential K Y n r a s)) =
      (-1 : ℤ) ^ (n + 3 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1 + (r + 1)) Y.basepoint)))
        (n + 1) (fun t ↦ Additive.ofMul (a t)) s := by
  apply eq_of_heq
  exact (coefficientIndexEquiv_toAdditive_heq Y _ _).trans
    (coefficientDifferential_all_alternating_heq K Y n r a s)

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
