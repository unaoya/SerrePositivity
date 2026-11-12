module

public import SerrePositivity.KST.Spectra.LoopMappingClasses
public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource
public import SerrePositivity.KST.Spectra.PathContractibility

/-!
概要：loop を値とする写像のホモトピー類の単位元と円の次数射の作用。
方針：二つの源の交換で、基本群における指定基本類の像の計算へ戻す。
規約：パラメータ源は任意、標的は Kan とする。
使われ方：Goerss–Jardine I §7、HA §1.4.2。有理 telescope の構造射の計算。
-/

@[expose] public section

universe u

open CategoryTheory SSet CartesianMonoidalCategory
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PointedMapping

/-- 概要：零射に対応する写像空間の頂点は基点。
方針：常に基点を値とするパラメータ族の curry を計算する。
規約：Kan 性は不要。
使われ方：Goerss–Jardine I §7。写像の類の単位元の識別。 -/
@[simp]
theorem familyVertex_zero (X Y : PointedSimplicialSet.{u}) :
    familyVertex (0 : X ⟶ Y) =
      PointedSimplicialSet.basepoint (PointedObject.basedHom X Y) := by
  have h : CartesianMonoidalCategory.fst X.right (Δ[0] : SSet.{u}) ≫
      (0 : X ⟶ Y).right = toUnit _ ≫ Y.hom := by
    rw [PointedObject.zero_right, comp_toUnit_assoc]
  dsimp only [familyVertex, pointFamily]
  simp only [h]
  rw [paramCurry_constant, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const, yonedaEquiv_const]

end PointedMapping

namespace LoopMappingClasses

/-- 概要：基点で定数な射のホモトピー類は群の単位元。
方針：交換同型の後で定数射の基本群への作用を計算する。
規約：Y は Kan、パラメータ源 A は任意。
使われ方：Goerss–Jardine I §7。ホモトピー類の積を表す射の単位則。 -/
@[simp]
theorem classOf_zero (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    classOf (0 : A ⟶ PointedObject.basedHom CirclePower.space.{u} Y) = 1 := by
  apply (groupEquiv A Y).injective
  rw [map_one, groupEquiv_apply]
  let e : PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y
  change CirclePower.componentEquiv (PointedObject.basedHom A Y)
    (mapπ₀ e.hom.right (π₀.mk (PointedMapping.familyVertex 0))) = 1
  rw [mapπ₀_mk, PointedMapping.familyVertex_zero,
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint e.hom,
    ← PointedMapping.familyVertex_zero CirclePower.space (PointedObject.basedHom A Y),
    CirclePower.componentEquiv_familyVertex]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
    (0 : CirclePower.space.{u} ⟶ PointedObject.basedHom A Y).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) CirclePower.generator = 1
  simp only [PointedObject.zero_right, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.map_const 1 _ CirclePower.generator

/-- 概要：円の次数射の後合成は任意のパラメータを持つ loop の類に m 乗で作用する。
方針：第二の源の制限自然性で円の成分比較へ移し、その冪作用を使う。
規約：この段階はホモトピー類の群の演算で述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2。有理化の実際の次数射の作用。 -/
theorem post_power (A Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (m : ℕ) (a : LoopMappingClasses A Y) :
    mapπ₀ (PointedObject.basedHomMap A
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m) Y)).right a = a ^ m := by
  apply (groupEquiv A Y).injective
  rw [map_pow, groupEquiv_apply, groupEquiv_apply]
  have hs := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeSecondSource.natural_pre_right
    (C := PointedSimplicialSet.{u}) A (CirclePower.powerMap.{u} m) Y
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hs
  let e : PointedObject.basedHom A (PointedObject.basedHom CirclePower.space.{u} Y) ≅
      PointedObject.basedHom CirclePower.space (PointedObject.basedHom A Y) :=
    _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A CirclePower.space Y
  change PointedObject.basedHomMap A
      (Y := PointedObject.basedHom CirclePower.space Y)
      (Z := PointedObject.basedHom CirclePower.space Y)
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m) Y) ≫ e.hom =
    e.hom ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.powerMap m)
      (PointedObject.basedHom A Y) at hs
  have hπ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.mapPiZero_square _ _ e.hom.right e.hom.right
    (congrArg Under.Hom.right hs) a
  change CirclePower.componentEquiv (PointedObject.basedHom A Y)
    (mapπ₀ e.hom.right (mapπ₀ _ a)) = _
  rw [hπ, CirclePower.componentEquiv_pre_power]
  rfl

end LoopMappingClasses

end

end SerrePositivity.KST.Spectra
