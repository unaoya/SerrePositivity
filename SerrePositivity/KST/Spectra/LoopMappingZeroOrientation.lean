module

public import SerrePositivity.KST.Spectra.LoopZeroOrientation
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSymmetry
public import SerrePositivity.KST.Spectra.LoopMappingPositiveEquiv
public import SerrePositivity.KST.Spectra.LoopMappingClasses
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-!
概要：円の Kan 置換を用いた写像類と、通常の零 loop 同値の向きの照合。
方針：置換単位による制限と内部 Hom の交換を可換にし、円の成分表示の逆元式を使う。
規約：二つの loop 模型の相違を明示した比較を用いる。
使われ方：Goerss–Jardine I §7–8、VIII §1。既存の基本群係数表示の基本段。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalClosed SSet

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 円の置換単位への制限後の零 loop 比較は、既存の円の成分表示の逆元。 -/
lemma CirclePower.loopZero_pre_unit (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : π₀ (PointedObject.basedHom space.{u} Y).right) :
    loopZeroHomotopyEquiv Y (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed unit Y).right a)) = (componentEquiv Y a)⁻¹ := by
  rw [loopZeroHomotopyEquiv_eq_inv_component, Equiv.apply_symm_apply]
  rfl

namespace PointedMapping

/-- 通常の loop 値の成分と元の写像空間の基本群の同値。 -/
def loopZeroComponentEquiv (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    π₀ (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A Y).right 0
        (PointedSimplicialSet.basepoint (PointedObject.basedHom A Y)) :=
  (π₀Functor.mapIso (PointedSimplicialSet.forget.mapIso (loopSwap A Y).symm)).toEquiv.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm.trans (loopZeroHomotopyEquiv (PointedObject.basedHom A Y)))

lemma loopZeroComponentEquiv_apply (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : π₀ (PointedObject.basedHom A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) :
    loopZeroComponentEquiv A Y a = loopZeroHomotopyEquiv (PointedObject.basedHom A Y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero.symm (mapπ₀ (loopSwap A Y).inv.right a)) := rfl

/-- 概要：通常の loop の成分比較と既存の Kan 円の写像類の比較は逆元で相違する。
方針：置換単位と源の交換の可換正方形を π₀ へ送り、零 loop の逆元公式を適用する。
規約：パラメータの源 A は任意。
使われ方：Goerss–Jardine VIII §1。セル球面の基本群表示との接続。 -/
theorem loopZeroComponentEquiv_unit (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : LoopMappingClasses A Y) :
    loopZeroComponentEquiv A Y (mapπ₀
      (PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y)).right a) =
      (LoopMappingClasses.classEquiv A Y a)⁻¹ := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) A CirclePower.unit Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A PointedSimplicialSet.circle.{u} Y).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Y).hom ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit (PointedObject.basedHom A Y) at hs
  rw [_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.hom_eq_inv] at hs
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Y).hom.right
    (loopSwap A Y).inv.right (congrArg Under.Hom.right hs) a
  rw [loopZeroComponentEquiv_apply, hπ, CirclePower.loopZero_pre_unit]
  rfl

/-- 円の置換単位の後合成は、パラメータ付き写像空間の成分で全単射。 -/
lemma loopUnit_post_piZero_bijective (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    Function.Bijective (mapπ₀
      (PointedObject.basedHomMap A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y)).right) := by
  have hp := post_rlp_monomorphisms A (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.anodyne_prePointed_rlp CirclePower.unit
      (PointedKanReplacement.unit_anodyne PointedSimplicialSet.circle.{u}) Y)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ hp).piZero_bijective_at
    (PointedSimplicialSet.basepoint
      (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y)))

/-- 概要：通常の零 loop 成分比較は源の射への制限と可換。
方針：成分を Kan 円の写像類へ持ち上げ、既存の源自然性と逆元保存を使う。
規約：源の射に単射性は不要。
使われ方：Goerss–Jardine VIII §1。セル球面への制限と零次数比較の交換。 -/
theorem loopZeroComponentEquiv_pre {A B : PointedSimplicialSet.{u}} (i : A ⟶ B)
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (a : π₀ (PointedObject.basedHom B (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right) :
    loopZeroComponentEquiv A Y (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right a) =
      pointedGroupMap 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y) (loopZeroComponentEquiv B Y a) := by
  obtain ⟨c, rfl⟩ := (loopUnit_post_piZero_bijective B Y).2 a
  have hs := prePointed_post i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed CirclePower.unit Y)
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (PointedObject.basedHom CirclePower.space.{u} Y)).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y)).right (congrArg Under.Hom.right hs.symm) c
  rw [hπ, loopZeroComponentEquiv_unit, loopZeroComponentEquiv_unit]
  rw [LoopMappingClasses.classEquiv_pre, map_inv]
  rfl

end PointedMapping
end
end SerrePositivity.KST.Spectra
