module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Monotone.Defs

/-!
分割で生成：docstring を書き直すこと
概要：元の正方形を下辺・共通対角・上辺の合成三角形で分解する形状写像。
方針：有限格子の単調写像で、二つの三角形への退化写像と全合成族を構成する。
規約：正方形の向きは第一因子が辺、第二因子が比較。使われ方：全 h Fun の右辺分解。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
end SerrePositivity.KST.LocalizingInvariants.SquareDiagonal
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants.SquareDiagonal

def postIndex : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 0 then 0 else if p.2 = 0 then 1 else 2
  monotone' := by decide

def preIndex : Fin 2 × Fin 2 →o Fin 3 where
  toFun p := if p.1 = 1 then 2 else p.2.castSucc
  monotone' := by decide

def factorIndex : Fin 2 × Fin 3 →o Fin 2 where
  toFun p := if p.2 = 0 then 0 else if p.2 = 1 then p.1 else 1
  monotone' := by decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
