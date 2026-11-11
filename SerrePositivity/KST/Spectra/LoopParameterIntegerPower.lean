module

public import SerrePositivity.KST.Spectra.LoopIntegerPower

/-!
概要：二つの Kan 円を源とする写像の成分で、いずれの円の整数次数射も同じ整数冪で作用する。
方針：パラメータ源の自然性を写像空間の基本群へ移す。
規約：ホモトピー類の群は実証済みの LoopMappingClasses のもの。
使われ方：Goerss–Jardine I §7、BF 1978 §2。二つの loop 変数の符号反転の比較。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.LoopMappingClasses

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Kan 円のパラメータの整数次数射は二重 loop の類に整数冪で作用する。
方針：パラメータ制限の基本群との自然性と正次数群での次数射の作用を使う。
規約：標的 Y は Kan、整数 z は任意。
使われ方：Goerss–Jardine I §7。二つの円のどちらで符号を反転するかの比較。 -/
theorem pre_integer (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) (a : LoopMappingClasses CirclePower.space.{u} Y) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z)
      (PointedObject.basedHom CirclePower.space.{u} Y)).right a = a ^ z := by
  apply (groupEquiv CirclePower.space Y).injective
  rw [map_zpow, groupEquiv_apply, groupEquiv_apply, classEquiv_pre]
  exact groupMap_pre_integer Y z 0 (classEquiv CirclePower.space Y a)

/-- 概要：二重 loop の成分では二つの円の整数次数射の作用は一致する。
方針：両方が同じ整数冪に作用する式を比較する。
規約：実際の写像空間の π₀ 上の関数の等式。
使われ方：BF 1978 §2、HA §1.4.2。符号を置く loop 変数の交換。 -/
theorem pre_integer_eq_post_integer (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
    (z : ℤ) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z)
      (PointedObject.basedHom CirclePower.space.{u} Y)).right =
      mapπ₀ (PointedObject.basedHomMap CirclePower.space.{u}
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap z) Y)).right := by
  funext a
  exact (pre_integer Y z a).trans (post_integerPower CirclePower.space Y z a).symm

end

end SerrePositivity.KST.Spectra.LoopMappingClasses
