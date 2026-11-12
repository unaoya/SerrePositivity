module

public import SerrePositivity.KST.Spectra.CircleMappingComponents
public import SerrePositivity.KST.Spectra.LoopHomotopyGroups

/-!
概要：円の Kan 置換からの Hom の正次数群は標的の一つ高い次数の群である。
方針：円の置換単位の前合成の π_* 同型と loop の連結群同型を合成する。
規約：標的は点つき Kan 複体。次数 n は実際の n+1。
使われ方：Goerss–Jardine I §7、VIII §1。球面の Hom の群の次数移動。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.CirclePower

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の Kan 置換からの Hom の正次数の標準群同型。
方針：anodyne 単位による制限の群同型を通常の loop の次数移動へ合成する。
規約：π_(n+1) の Hom を π_(n+2) の標的へ移す。
使われ方：Goerss–Jardine I §7、VIII §1。loop 値の球面の群の比較の終段。 -/
def positiveHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom space.{u} Y).right n
        (PointedSimplicialSet.basepoint (PointedObject.basedHom space Y)) ≃*
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1) Y.basepoint := by
  let f : PointedObject.basedHom space.{u} Y ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y :=
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y
  have hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp unit
        (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Y)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n f.right hf
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint f)).trans (loopPositiveHomotopyEquiv Y n)

end

end SerrePositivity.KST.Spectra.CirclePower
