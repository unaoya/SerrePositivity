module

public import SerrePositivity.KST.Spectra.CirclePowerPositiveHomotopy
public import SerrePositivity.KST.Spectra.PositiveLoopNaturality

/-!
概要：円の Kan 置換の Hom の正次数の群同型の係数の自然性。
方針：anodyne 単位の前合成の自然性と通常の loop の自然性を合成する。
規約：実際の係数の点つき射からの誘導群準同型を比較する。
使われ方：Goerss–Jardine I §7、VIII §1。球面の群の比較の基本段の自然性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra.CirclePower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma positiveHomotopyEquiv_formula (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom space Y))) :
    positiveHomotopyEquiv Y n a =
      loopPositiveHomotopyEquiv Y n (pointedGroupMap
        (X := PointedObject.basedHom space Y) (Y := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) n
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y) a) := by
  simp only [positiveHomotopyEquiv, MulEquiv.trans_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism_apply]
  rfl

/-- 概要：円の Kan 置換の Hom の群の次数移動は係数射と可換。
方針：前合成の標的自然性を群へ送り、通常の loop の群の自然性へ合成する。
規約：係数は点つき Kan 複体。
使われ方：Goerss–Jardine I §7、VIII §1。球面の Hom の群の自然な比較。 -/
theorem positiveHomotopyEquiv_natural {Y Z : PointedSimplicialSet.{u}}
    [KanComplex Y.right] [KanComplex Z.right] (p : Y ⟶ Z) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom space.{u} Y).right n
      (PointedSimplicialSet.basepoint (PointedObject.basedHom space Y))) :
    positiveHomotopyEquiv Z n (pointedGroupMap
        (X := PointedObject.basedHom space Y) (Y := PointedObject.basedHom space Z) n
          (PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) p) a) =
      pointedGroupMap (n + 1) p (positiveHomotopyEquiv Y n a) := by
  have h := (MonoidalClosed.pre unit.{u}).naturality p
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  change PointedObject.basedHomMap space.{u} (Y := Y) (Z := Z) p ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Z =
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y ≫
      PointedObject.basedHomMap PointedSimplicialSet.circle.{u} (Y := Y) (Z := Z) p at h
  have hg := congrArg (fun f ↦ pointedGroupMap n f a) h
  simp only [pointedGroupMap_comp] at hg
  rw [positiveHomotopyEquiv_formula, positiveHomotopyEquiv_formula, hg]
  exact loopPositiveHomotopyEquiv_natural p n _

end

end SerrePositivity.KST.Spectra.CirclePower
