module

public import SerrePositivity.KST.Spectra.LoopIntegerPower
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource

/-!
概要：loop の整数冪の射の後合成は、パラメータ付き写像空間の正次数群に整数冪で作用する。
方針：内部 Hom の交換で円の次数射の前合成へ移す。
規約：パラメータ源の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの三角形の交換と loop の逆元の射の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：円の整数次数射の前合成を後合成すると写像空間の正次数群に整数冪で作用する。
方針：源二つの交換同型とその自然性で既知の次数射の作用へ戻す。
規約：A は任意、Y は Kan、次数は n+1。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop 値の写像空間の基本群での逆元の計算。 -/
theorem groupMap_post_integer (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (PointedObject.basedHom A
      (PointedObject.basedHom CirclePower.space.{u} Y)).right n
        (PointedSimplicialSet.basepoint (PointedObject.basedHom A
          (PointedObject.basedHom CirclePower.space Y)))) :
    pointedGroupMap n (PointedObject.basedHomMap A
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y)) a = a ^ z := by
  have : KanComplex (PointedSimplicialSet.forget.obj
      (PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex A (PointedObject.basedHom CirclePower.space Y)
  have : KanComplex (PointedSimplicialSet.forget.obj
      (PointedObject.basedHom CirclePower.space.{u} (PointedObject.basedHom A Y))) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex CirclePower.space (PointedObject.basedHom A Y)
  let e : PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y
  have hinj : Function.Injective (pointedGroupMap n e.hom) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n e.hom.right
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso (PointedSimplicialSet.forget.mapIso e))
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e.hom)).injective
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) A (CirclePower.integerPowerMap.{u} z) Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  change PointedObject.basedHomMap A
      (Y := PointedObject.basedHom CirclePower.space Y)
      (Z := PointedObject.basedHom CirclePower.space Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) ≫ e.hom =
    e.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z)
      (PointedObject.basedHom A Y) at hs
  apply hinj
  rw [map_zpow, ← pointedGroupMap_comp, hs, pointedGroupMap_comp]
  exact groupMap_pre_integer (PointedObject.basedHom A Y) z n (pointedGroupMap n e.hom a)

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
