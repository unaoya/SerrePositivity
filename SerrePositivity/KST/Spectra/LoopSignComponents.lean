module

public import SerrePositivity.KST.Spectra.LoopMappingTargetNaturality
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-!
概要：パラメータを持つ反復 loop の符号反転の二回合成。
方針：整数冪の後合成の成分での作用を実際の射の代表で計算する。
規約：二回合成を厳密恒等とは主張せず、点つき射の成分で比較する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。符号を調整した loop 列の構造可換式。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：反復 loop 値の射に標的の loop の整数冪を後合成すると類の整数冪となる。
方針：パラメータ付き写像空間の成分の式をその射の頂点で評価する。
規約：源 A に Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。二回の符号反転の成分での計算。 -/
theorem LoopMappingClasses.classOf_comp_nested_integer {A Z : PointedSimplicialSet.{u}}
    [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Z)) (z : ℤ) :
    LoopMappingClasses.classOf (f ≫ PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} z) Z)) =
      LoopMappingClasses.classOf f ^ z := by
  have h := LoopMappingClasses.post_target_integer A Z z (LoopMappingClasses.classOf f)
  change mapπ₀ (PointedObject.basedHomMap A
    (PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} z) Z))).right
        (π₀.mk (PointedMapping.familyVertex f)) = _ at h
  rw [mapπ₀_mk, PointedMapping.familyVertex_post] at h
  exact h

/-- 概要：反復 loop 値の射の後で内側の loop の符号を二度反転しても同じ成分となる。
方針：各反転が類の群の逆元であることを二度適用する。
規約：任意の源のパラメータを保つ。
使われ方：BF 1978 §2、HA §1.4.2。交換で得た符号と構造射の符号を打ち消す。 -/
theorem PointedMapping.componentOf_nested_neg_one_twice {A Z : PointedSimplicialSet.{u}}
    [KanComplex Z.right]
    (f : A ⟶ PointedObject.basedHom CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Z)) :
    PointedMapping.componentOf ((f ≫ PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z)) ≫
        PointedObject.basedHomMap CirclePower.space.{u}
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1)) Z)) =
      PointedMapping.componentOf f := by
  change LoopMappingClasses.classOf _ = LoopMappingClasses.classOf f
  rw [LoopMappingClasses.classOf_comp_nested_integer,
    LoopMappingClasses.classOf_comp_nested_integer, zpow_neg_one, zpow_neg_one, inv_inv]

end

end SerrePositivity.KST.Spectra
