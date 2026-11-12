module

public import SerrePositivity.KST.Spectra.SkeletalCoefficientAlternatingZero
public import SerrePositivity.KST.Spectra.SkeletalCoefficientLoopDifferential

/-!
概要：正次数の群の係数微分を通常の正規化交代微分で計算する。
方針：基本段の交代式から、loop の反可換式と係数自然性で帰納する。
規約：cochain 次数二以上。各次数移動で生じる負符号を保持する。
使われ方：Goerss–Jardine VIII §1。骨格の係数複体の同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 等しい次数の間で、loop の加法表示とその負元は異種等式を保つ。 -/
lemma loopPositive_neg_heq (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    {m k : ℕ} (h : m = k)
    (a : Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right m (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))
    (b : Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right k (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))
    (hab : HEq a b) :
    HEq (-(loopPositiveHomotopyEquiv Y m).toAdditive a)
      (-(loopPositiveHomotopyEquiv Y k).toAdditive b) := by
  subst k
  cases hab
  rfl

set_option maxRecDepth 2048 in
-- loop の係数同型と係数微分の入力の別名を照合するため。
/-- 実際の群の係数微分は各高次数で符号付きの正規化交代微分。 -/
theorem coefficientDifferential_alternating_heq (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : coefficientGroup K Y (n + 1) (r + 1)) (s : K.nonDegenerate (n + 3)) :
    HEq (Additive.ofMul (coefficientDifferential K Y (n + 1) r a s))
      (      (-1 : ℤ) ^ (n + 4 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2 + (r + 1)) Y.basepoint)))
        (n + 2) (fun t ↦ Additive.ofMul (a t)) s) := by
  induction r generalizing Y with
  | zero => exact heq_of_eq (coefficientDifferential_zero_alternating K Y n a s)
  | succ r ih =>
    let e := loopPositiveHomotopyEquiv Y (n + 2 + (r + 1))
    let c := fun t ↦ e.symm (a t)
    have hi : (fun t ↦ e (c t)) = a := by
      funext t
      exact e.apply_symm_apply _
    have hd := coefficientDifferential_loopPositive K Y (n + 1) r c s
    have hc := ih (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) c
    have hh := loopPositive_neg_heq Y
      (by omega : n + 1 + 1 + 1 + r = n + 2 + (r + 1)) _ _ hc
    have hm := NormalizedValueCochains.differential_map K
      (M := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right
        (n + 2 + (r + 1)) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)))
      (N := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
        (n + 2 + (r + 1) + 1) Y.basepoint)))
      e.toAdditive.toAddMonoidHom (n + 2) (fun t ↦ Additive.ofMul (c t)) s
    rw [hi] at hd
    have hd' : Additive.ofMul (coefficientDifferential K Y (n + 1) (r + 1) a s) =
        -(loopPositiveHomotopyEquiv Y (n + 1 + 1 + 1 + r)).toAdditive
          (Additive.ofMul (coefficientDifferential K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1) r c s)) :=
      congrArg Additive.ofMul hd
    apply (heq_of_eq hd').trans
    apply hh.trans
    apply heq_of_eq
    change -e.toAdditive _ = _
    rw [map_zsmul]
    have hmc := congrArg
      (fun z : Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2 + (r + 1) + 1) Y.basepoint) ↦
        -((-1 : ℤ) ^ (n + 4 + r) • z)) hm.symm
    apply hmc.trans
    have hia : (fun t ↦ e.toAdditive.toAddMonoidHom (Additive.ofMul (c t))) =
        (fun t ↦ Additive.ofMul (a t)) := by
      funext t
      exact congrArg Additive.ofMul (e.apply_symm_apply (a t))
    have hfinal := congrArg
      (fun q : K.nonDegenerate (n + 2) →
        Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2 + (r + 1) + 1) Y.basepoint) ↦
        -((-1 : ℤ) ^ (n + 4 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
          (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
            (n + 2 + (r + 1) + 1) Y.basepoint))) (n + 2) q s)) hia
    apply hfinal.trans
    have hsign : -((-1 : ℤ) ^ (n + 4 + r)) = (-1 : ℤ) ^ (n + 4 + (r + 1)) := by
      simpa only [mul_neg_one, Nat.add_assoc] using (pow_succ (-1 : ℤ) (n + 4 + r)).symm
    exact (neg_smul ((-1 : ℤ) ^ (n + 4 + r)) _).symm.trans
      (congrArg (fun z : ℤ ↦ z • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right
          (n + 2 + (r + 1) + 1) Y.basepoint)))
        (n + 2) (fun t ↦ Additive.ofMul (a t)) s) hsign)

/-- 等しい自然数次数のホモトピー群の標準の添字同型。 -/
def coefficientIndexEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    {m k : ℕ} (h : m = k) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right m Y.basepoint ≃* _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right k Y.basepoint := by
  subst k
  exact MulEquiv.refl _

/-- 添字同型は加法表示の元を異種等式で保持する。 -/
lemma coefficientIndexEquiv_toAdditive_heq (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    {m k : ℕ} (h : m = k) (a : Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right m Y.basepoint)) :
    HEq ((coefficientIndexEquiv Y h).toAdditive a) a := by
  subst k
  rfl

/-- 次数の標準同定の後、群の係数微分は符号付きの通常の交代微分そのもの。 -/
theorem coefficientDifferential_alternating (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (a : coefficientGroup K Y (n + 1) (r + 1)) (s : K.nonDegenerate (n + 3)) :
    (coefficientIndexEquiv Y
      (by omega : n + 1 + 1 + 1 + r = n + 2 + (r + 1))).toAdditive
        (Additive.ofMul (coefficientDifferential K Y (n + 1) r a s)) =
      (-1 : ℤ) ^ (n + 4 + r) • _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 2 + (r + 1)) Y.basepoint)))
        (n + 2) (fun t ↦ Additive.ofMul (a t)) s := by
  apply eq_of_heq
  exact (coefficientIndexEquiv_toAdditive_heq Y _ _).trans
    (coefficientDifferential_alternating_heq K Y n r a s)

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
