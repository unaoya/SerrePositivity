module

public import SerrePositivity.EInfinity.BarrattEccles.Cotensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameRealizationLifting

/-!
# 右 frame の余テンソルの fibration

概要：Hovey §5.4 の余テンソルは単射を fibration、anodyne 射を自明 fibration に移す。
方針：反対圏での実現の持ち上げ定理を実際の E 代数モデルへ代入する。
規約：元の対象は任意の E 代数で、モデル構造の入力仮定なし。
使われ方：一般 homotopy 極限の重み付き錐と単体的切断。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits HomotopicalAlgebra

variable (A : Type u) [CommRing A]

local instance : HasColimitsOfSize.{0, u} (operad A).Algebraᵒᵖ :=
  hasColimitsOfSizeShrink.{0, u} _

/-- 概要：単射に沿う右 frame の余テンソルは fibration（BM 命題 4.1、Hovey §5.4）。
方針：反対圏での実現の cofibration 保存を使う。
規約：単体集合の完全なモデル構造を仮定しない。
使われ方：重みの部分単体集合への制限の全射性。 -/
lemma cotensor_map_fibration (X : (operad A).Algebra)
    {K L : SSet.{u}} (i : K ⟶ L) (hi : Mono i) :
    let := modelCategory A
    Fibration ((cotensor A X).map i.op) := by
  let := modelCategory A
  exact ⟨_root_.SerrePositivity.FrameRealizationLifting.FrameRealizationLifting.map_monomorphism (rightFrame A X)
    (rightFrame_cofibrant A X) i hi⟩

/-- 概要：anodyne 射に沿う余テンソルは自明 fibration（BM 命題 4.1、Hovey §5.4）。
方針：右 frame の全単体作用素の弱同値性と実現の anodyne 保存を使う。
規約：始域の cofibrancy や単体集合のモデルの存在は入力しない。
使われ方：ホーンと可縮な重みの付加に沿う余テンソルの比較。 -/
lemma cotensor_map_trivialFibration (X : (operad A).Algebra)
    {K L : SSet.{u}} (i : K ⟶ L) (hi : SSet.anodyneExtensions i) :
    let := modelCategory A
    trivialFibrations (operad A).Algebra ((cotensor A X).map i.op) := by
  let := modelCategory A
  exact _root_.SerrePositivity.FrameRealizationLifting.FrameRealizationLifting.map_anodyne (rightFrame A X)
    (rightFrame_cofibrant A X) (fun f => rightFrame_homotopicallyConstant A X f) i hi

end SerrePositivity.EInfinity.BarrattEccles
