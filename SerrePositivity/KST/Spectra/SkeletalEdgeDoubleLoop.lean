module

public import SerrePositivity.KST.Spectra.SkeletalEdgeAlternating
public import SerrePositivity.KST.Spectra.SkeletalZeroCoefficientDifferential
public import SerrePositivity.KST.Spectra.NormalizedValueNaturality

/-!
概要：次数一の二重 loop 係数から群の実際の係数微分へ交代式を移す。
方針：任意の次数一 cochain を実現し、二つの loop 同型と成分微分の式を合成する。
規約：零 loop の逆元を入力に保持する。
使われ方：Goerss–Jardine VIII §1。次数一の係数微分の基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open UnbasedPointedMapping

/-- 二重 loop の基本群と元の標的の三次ホモトピー群の標準同型。 -/
def edgeDoubleLoopCoefficientEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right 0
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint :=
  (loopPositiveHomotopyEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0).trans (loopPositiveHomotopyEquiv Y 1)

set_option maxRecDepth 2048 in
-- 二重 loop の fiber と通常の成分比較の別名を照合するため。
/-- 任意の次数一の二重 loop 係数の交代微分を、実際の群の係数微分で計算する。 -/
theorem edge_doubleLoop_normalizedDifferential (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (c : K.nonDegenerate 1 → _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right 0
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint) (s : K.nonDegenerate 2) :
    (edgeDoubleLoopCoefficientEquiv Y).toAdditive
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right 0
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint))) 1 (fun t ↦ Additive.ofMul (c t)) s) =
      Additive.ofMul (coefficientDifferential K Y 0 0
        (fun t ↦ (edgeDoubleLoopCoefficientEquiv Y (c t))⁻¹) s) := by
  obtain ⟨f, hf, hfc⟩ := SkeletalEdgeCochain.exists_realization K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)
    (fun t ↦ Additive.ofMul (c t))
  let v : π₀ (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) 0).right :=
    π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) 0 f hf)
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0).right 0
      (stageFiber K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0).basepoint :=
    stageFiberOrdinaryLoopComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 v
  have hc (t : K.nonDegenerate 1) :
      stageFiberComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)) 0 v t = c t := by
    have h := (SkeletalEdgeCochain.fiberVertex_cochain K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f hf).trans hfc
    exact congrArg (fun g ↦ Additive.toMul (g t)) h
  have hin : (fun t ↦ loopPositiveHomotopyEquiv Y 1
      (stageFiberCoefficientEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 0 b t)) =
      (fun t ↦ (edgeDoubleLoopCoefficientEquiv Y (c t))⁻¹) := by
    funext t
    rw [stageFiberCoefficientEquiv_loopZero, hc, map_inv]
    rfl
  have hd := coefficientDifferential_zero_component K Y 0 b s
  have hd' := (congrArg (fun q ↦ coefficientDifferential K Y 0 0 q s) hin).symm.trans hd
  have ha := edge_normalizedDifferential_stageComponent K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) f hf s
  rw [hfc] at ha
  have hh := congrArg (loopPositiveHomotopyEquiv Y 1).toAdditive ha
  exact hh.trans (congrArg
    (fun z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint ↦ Additive.ofMul z) hd'.symm)

set_option maxRecDepth 2048 in
-- 二重 loop の係数同型と係数微分の入力の別名を照合するため。
/-- 次数一の実際の係数微分の基本段は、通常の正規化微分の負元。 -/
theorem first_coefficientDifferential_zero_alternating (K : SSet.{u})
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : coefficientGroup K Y 0 1) (s : K.nonDegenerate 2) :
    Additive.ofMul (coefficientDifferential K Y 0 0 a s) =
      -_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint)))
        1 (fun t ↦ Additive.ofMul (a t)) s := by
  let e := edgeDoubleLoopCoefficientEquiv Y
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
  have h := edge_doubleLoop_normalizedDifferential K Y c s
  have hm := NormalizedValueCochains.differential_map K
    (M := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right
      0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).basepoint)))
    (N := AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint)))
    e.toAdditive.toAddMonoidHom 1 (fun t ↦ Additive.ofMul (c t)) s
  have hl : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint)))
      1 (fun t ↦ e.toAdditive (Additive.ofMul (c t))) s =
      -_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
        (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint)))
        1 (fun t ↦ Additive.ofMul (a t)) s := by
    rw [ha]
    change (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 2 Y.basepoint))) 1
      (-(fun t ↦ Additive.ofMul (a t)))) s = _
    rw [map_neg]
    rfl
  have hh := hl.symm.trans (hm.trans h)
  rw [hi] at hh
  exact hh.symm

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
