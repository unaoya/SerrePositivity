module

public import SerrePositivity.KST.Spectra.CircleClassMap
public import SerrePositivity.KST.Spectra.LoopMappingOperations

/-!
概要：整数次数の円の自己射の写像空間の成分への作用。
方針：指定基本類の像と内部 Hom の二つの源の交換で計算する。
規約：負の整数を含む。高次群の作用は別途比較する。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop の符号の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：整数次数の円の射の前合成は成分比較の下で整数冪。
方針：成分を実際の射で表して指定基本類の像を計算する。
規約：Y は Kan、z は任意の整数。
使われ方：Goerss–Jardine I §7。負の次数射のパラメータつき作用。 -/
theorem CirclePower.componentEquiv_pre_integer (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (z : ℤ) (a : π₀ (PointedObject.basedHom CirclePower.space.{u} Y).right) :
    CirclePower.componentEquiv Y
      (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y).right a) =
        CirclePower.componentEquiv Y a ^ z := by
  obtain ⟨v, rfl⟩ := π₀.mk_surjective a
  obtain ⟨f, rfl⟩ := (PointedMapping.familyVertexEquiv CirclePower.space Y).surjective v
  change CirclePower.componentEquiv Y
    (mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y).right
      (π₀.mk (PointedMapping.familyVertex f))) =
    CirclePower.componentEquiv Y (π₀.mk (PointedMapping.familyVertex f)) ^ z
  rw [mapπ₀_mk, PointedMapping.familyVertex_pre,
    CirclePower.componentEquiv_familyVertex, CirclePower.componentEquiv_familyVertex]
  exact CirclePower.evaluateGenerator_integerPower f z

/-- 概要：整数次数の円の射は任意のパラメータを持つ loop の類に整数冪で作用する。
方針：第二の源の制限と交換同型の自然性を成分比較へ合成する。
規約：A は任意、Y は Kan、z は任意の整数。
使われ方：Goerss–Jardine I §7、HA §1.4.2。loop の符号を表す実際の射の識別。 -/
theorem LoopMappingClasses.post_integerPower (A Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] (z : ℤ) (a : LoopMappingClasses A Y) :
    mapπ₀ (PointedObject.basedHomMap A
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y)).right a = a ^ z := by
  apply (LoopMappingClasses.groupEquiv A Y).injective
  rw [map_zpow, LoopMappingClasses.groupEquiv_apply, LoopMappingClasses.groupEquiv_apply]
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) A (CirclePower.integerPowerMap.{u} z) Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  let e : PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y
  change PointedObject.basedHomMap A
      (Y := PointedObject.basedHom CirclePower.space Y)
      (Z := PointedObject.basedHom CirclePower.space Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y) ≫ e.hom =
    e.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z)
      (PointedObject.basedHom A Y) at hs
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _ e.hom.right e.hom.right
    (congrArg Under.Hom.right hs) a
  change CirclePower.componentEquiv (PointedObject.basedHom A Y)
    (mapπ₀ e.hom.right (mapπ₀ _ a)) = _
  rw [hπ, CirclePower.componentEquiv_pre_integer]
  rfl

end

end SerrePositivity.KST.Spectra
