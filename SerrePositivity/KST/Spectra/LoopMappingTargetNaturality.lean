module

public import SerrePositivity.KST.Spectra.LoopMappingClasses
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.KST.Spectra.PostLoopIntegerPower

/-!
概要：loop 値のホモトピー類と基本群の比較の標的の自然性。
方針：源の交換の標的の自然性と円の成分比較の自然性を合成する。
規約：パラメータ源は任意、標的は Kan。
使われ方：Goerss–Jardine I §7、HA §1.4.2。反復 loop の符号を置く変数の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：loop 値の類と写像空間の基本群の比較は標的の写像について自然。
方針：内部 Hom の交換の可換式を π₀ へ送り、円の基本群との比較へ合成する。
規約：A は任意の点つき単体集合。
使われ方：Goerss–Jardine I §7。反復 loop の冪の作用の通常の群への移送。 -/
theorem classEquiv_post (A : PointedSimplicialSet.{u})
    {Y Z : PointedSimplicialSet.{u}} [KanComplex Y.right] [KanComplex Z.right]
    (f : Y ⟶ Z) (a : LoopMappingClasses A Y) :
    classEquiv A Z (mapπ₀ (PointedObject.basedHomMap A
      (PointedObject.basedHomMap CirclePower.space.{u} f)).right a) =
      pointedGroupMap 0 (PointedObject.basedHomMap A f) (classEquiv A Y a) := by
  let eY := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Y
  let eZ := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space.{u} Z
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post
    (C := PointedSimplicialSet.{u}) A CirclePower.space.{u} f
  change PointedObject.basedHomMap A
      (Y := PointedObject.basedHom CirclePower.space.{u} Y)
      (Z := PointedObject.basedHom CirclePower.space.{u} Z)
      (PointedObject.basedHomMap CirclePower.space.{u} (Y := Y) (Z := Z) f) ≫
      eZ.hom = eY.hom ≫ PointedObject.basedHomMap CirclePower.space.{u}
        (Y := PointedObject.basedHom A Y) (Z := PointedObject.basedHom A Z)
        (PointedObject.basedHomMap A (Y := Y) (Z := Z) f) at hs
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _ eY.hom.right eZ.hom.right
    (congrArg Under.Hom.right hs) a
  change CirclePower.componentEquiv (PointedObject.basedHom A Z)
    (mapπ₀ eZ.hom.right (mapπ₀ _ a)) = _
  rw [hπ, CirclePower.componentEquiv_natural]
  rfl

/-- 概要：標的自身が loop 値の場合、その loop の整数冪も類の群に同じ整数冪で作用する。
方針：標的の自然性を使い、写像空間の正次数群での後合成の冪の式に戻す。
規約：A は任意、Z は Kan。
使われ方：Goerss–Jardine I §7、HA §1.4.2。三つの loop 変数の符号反転の照合。 -/
theorem post_target_integer (A Z : PointedSimplicialSet.{u}) [KanComplex Z.right]
    (z : ℤ) (a : LoopMappingClasses A (PointedObject.basedHom CirclePower.space.{u} Z)) :
    mapπ₀ (PointedObject.basedHomMap A (PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} z) Z))).right a = a ^ z := by
  apply (groupEquiv A (PointedObject.basedHom CirclePower.space Z)).injective
  rw [map_zpow, groupEquiv_apply, groupEquiv_apply, classEquiv_post]
  exact groupMap_post_integer A Z z 0
    (classEquiv A (PointedObject.basedHom CirclePower.space Z) a)

/-- 概要：標的の loop の次数射と類を定める loop の次数射は同じ成分の作用となる。
方針：両方の作用が類の群の同じ整数冪となる式を比較する。
規約：二つの射は異なる loop 変数を動かす。
使われ方：BF 1978 §2、HA §1.4.2。変数交換で得た符号を構造射の loop 変数へ移す。 -/
theorem target_integer_eq_inner_integer (A Z : PointedSimplicialSet.{u}) [KanComplex Z.right]
    (z : ℤ) :
    mapπ₀ (PointedObject.basedHomMap A (PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} z) Z))).right =
      mapπ₀ (PointedObject.basedHomMap A
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} z)
          (PointedObject.basedHom CirclePower.space.{u} Z))).right := by
  funext a
  exact (post_target_integer A Z z a).trans
    (post_integerPower A (PointedObject.basedHom CirclePower.space Z) z a).symm

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
