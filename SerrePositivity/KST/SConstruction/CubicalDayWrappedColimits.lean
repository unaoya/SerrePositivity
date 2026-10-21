module
public import SerrePositivity.KST.SConstruction.CubicalDayColimits

/-! # Day 圏での元の tensor の余極限保存
概要：元の前層と同じ Day 圏でも、左右の tensor 関手は余極限を保つ。
方針：元の圏同値と、証明済みの前層上の左右の余極限保存を合成する。
規約：元の対象・射を変えない。使われ方：cubical 合成の結合と単位の判定。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits

/-- 元の Day 圏で、左因子を固定した tensor は余極限を保つ。 -/
instance cubicalDayWrappedLeft_preservesColimits (K : CubicalDaySet.{u}) :
    PreservesColimitsOfSize.{u, u} (tensorLeft K) := by
  change PreservesColimitsOfSize.{u, u}
    (cubicalDayEquivalence.functor ⋙ cubicalDayTensorLeft K.functor ⋙
      cubicalDayEquivalence.inverse)
  infer_instance

/-- 元の Day 圏で、右因子を固定した tensor は余極限を保つ。 -/
instance cubicalDayWrappedRight_preservesColimits (K : CubicalDaySet.{u}) :
    PreservesColimitsOfSize.{u, u} (tensorRight K) := by
  change PreservesColimitsOfSize.{u, u}
    (cubicalDayEquivalence.functor ⋙ cubicalDayTensorRight K.functor ⋙
      cubicalDayEquivalence.inverse)
  infer_instance

end SerrePositivity.KST.SConstruction
