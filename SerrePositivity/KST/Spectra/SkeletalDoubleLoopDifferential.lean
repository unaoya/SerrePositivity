module

public import SerrePositivity.KST.Spectra.SkeletalLoopAlternating
public import SerrePositivity.KST.Spectra.SkeletalZeroCoefficientDifferential
public import SerrePositivity.KST.Spectra.SkeletalStrictRealization
public import SerrePositivity.KST.Spectra.NormalizedValueNaturality

/-!
概要：二重 loop の成分から群の実際の係数微分へ交代式を移す。
方針：任意の cochain の厳密な実現に成分微分の式を適用し、零 loop の二つの比較を合成する。
規約：cochain 次数二以上。零 loop の逆元を入力に明示する。
使われ方：Goerss–Jardine VIII §1。通常の群の係数微分の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping

/-- 二重 loop の高次係数と元の標的の二つ高い次数の係数の群同型。 -/
def doubleLoopCoefficientEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right (n + 1)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint :=
  (loopPositiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1)).trans
    (loopPositiveHomotopyEquiv Y (n + 2))

set_option maxRecDepth 2048 in
-- 二重 loop の fiber と通常の成分比較の別名を照合するため。
/-- 任意の二重 loop 係数の交代微分を、群の係数微分の値と符号付きで比較する。 -/
theorem doubleLoop_normalizedDifferential (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ)
    (c : K.nonDegenerate (n + 2) → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right (n + 1)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint) (s : K.nonDegenerate (n + 3)) :
    (doubleLoopCoefficientEquiv Y n).toAdditive
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right (n + 1)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint))) (n + 2) (fun t ↦ Additive.ofMul (c t)) s) =
      (-1 : ℤ) ^ (n + 3) • Additive.ofMul
        (coefficientDifferential K Y (n + 1) 0
          (fun t ↦ (doubleLoopCoefficientEquiv Y n (c t))⁻¹) s) := by
  obtain ⟨f, hf, hfc⟩ := SkeletalSphericalRealization.exists_strict_realization
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (fun t ↦ Additive.ofMul (c t))
  let v : π₀ (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (n + 1)).right :=
    π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (n + 1) f hf)
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1)).right 0
      (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1)).basepoint :=
    stageFiberOrdinaryLoopComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1) v
  have hc (t : K.nonDegenerate (n + 2)) :
      stageFiberComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) (n + 1) v t = c t := by
    have h := (skeletalFiberVertex_cochain K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) n f hf).trans hfc
    exact congrArg (fun g ↦ Additive.toMul (g t)) h
  have hin : (fun t ↦ loopPositiveHomotopyEquiv Y (n + 2)
      (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) (n + 1) 0 b t)) =
      (fun t ↦ (doubleLoopCoefficientEquiv Y n (c t))⁻¹) := by
    funext t
    rw [stageFiberCoefficientEquiv_loopZero, hc, map_inv]
    rfl
  have hd := coefficientDifferential_zero_component K Y (n + 1) b s
  have hd' := (congrArg (fun q ↦ coefficientDifferential K Y (n + 1) 0 q s) hin).symm.trans hd
  have ha := normalizedDifferential_stageComponent K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f hf s
  rw [hfc] at ha
  have hh := congrArg (loopPositiveHomotopyEquiv Y (n + 2)).toAdditive ha
  rw [map_zsmul] at hh
  exact hh.trans (congrArg (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 3) Y.basepoint ↦
    (-1 : ℤ) ^ (n + 3) • Additive.ofMul z) hd'.symm)

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
