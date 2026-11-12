module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.NatIso

/-!
# 小さい添字形状の二段の宇宙持ち上げ

## 概要
宇宙0の添字形状を係数環の宇宙経由で持ち上げたものと、一度で持ち上げたものを同定する。

## 方針
各次数で二重の ULift と一重の ULift を交換する。

## 規約
単体圏の作用と元の単体は変えない。

## 使われ方
HTT 4.2.4.1、Kerodon 7.5（Tag 039Y）。Δ・Δᵒᵖ の図式を dg bar の小さい添字へ渡す。
-/

@[expose] public section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 係数の宇宙を経由する添字形状の持ち上げと、直接の持ち上げの同型。 -/
def smallDiagramShapeIso (K : SSet.{0}) :
    (SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj K) ≅
      (SSet.uliftFunctor.{u + 1, 0}).obj K :=
  NatIso.ofComponents (fun _ => Equiv.toIso {
    toFun s := ULift.up s.down.down
    invFun s := ULift.up (ULift.up s.down)
    left_inv _ := rfl
    right_inv _ := rfl }) (fun _ => rfl)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
