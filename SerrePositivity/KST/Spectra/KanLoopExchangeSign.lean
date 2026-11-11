module

public import SerrePositivity.KST.Spectra.DoubleCircleLoopExchange
public import SerrePositivity.KST.Spectra.LoopMappingTargetNaturality

/-!
概要：loop 値の二重 Kan 円の交換の符号を内側の源の変数へ移す。
方針：標的の loop と類を定める loop の次数射が同じ冪に作用することを使う。
規約：成分上の関数の等式として述べる。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Ω スペクトルの構造射との符号の整合性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

/-- 概要：loop 値の二つの Kan 円の交換は内側の円の符号反転と成分で一致する。
方針：標的の loop の符号反転との比較の後で、符号を内側の源の変数へ移す。
規約：符号反転は Kan 円の整数次数 -1 の実際の射。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの符号を調整する構造射。 -/
theorem kanLoop_exchange_sign (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso CirclePower.space.{u} CirclePower.space.{u}
      (PointedObject.basedHom CirclePower.space.{u} Z)).hom.right =
    mapπ₀ (PointedObject.basedHomMap CirclePower.space.{u}
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (CirclePower.integerPowerMap.{u} (-1))
        (PointedObject.basedHom CirclePower.space.{u} Z))).right :=
  (kanDoubleCircleLoop_exchange Z).trans
    (LoopMappingClasses.target_integer_eq_inner_integer CirclePower.space.{u} Z (-1))

end

end SerrePositivity.KST.Spectra
