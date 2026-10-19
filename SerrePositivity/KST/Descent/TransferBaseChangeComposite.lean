module

public import SerrePositivity.KST.Descent.TransferBaseChange
public import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# 底変換した transfer の合成の指定一致

## 概要
底変換後の pullback と transfer の合成が、元の自然な合成の制限に一致することを証明する。

## 方針
二重引き戻しの指定前層同型が保つ pullback の式を、transfer の定義へ適用する。

## 規約
rank や値域の線形性は使用しない。

## 使われ方
論文 公理 (4)、補題 3.2 の同じ局所 rank 公式から全底変換の実降下を得る接続。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {V : Type w} [Category.{t} V] {X Y Z : C}
  (f : X ⟶ Y) (g : Z ⟶ Y) (F : Cᵒᵖ ⥤ V)

/-- 概要：底変換後の合成は元の合成の制限に厳密に一致（補題 3.2）。
方針：指定 pullback の比較式と transfer の定義を合成する。
規約：各対象だけでなく自然変換の等式。使われ方：全底変換での合成の弱同値の供給。 -/
theorem BaseChangeTransfer.baseChange_composite (tr : BaseChangeTransfer f F) :
    baseChangePresheafPullback (pullback.snd f g) F ≫
        (BaseChangeTransfer.baseChange f g F tr).transfer =
      Functor.whiskerLeft (Over.map g).op (baseChangePresheafPullback f F ≫ tr.transfer) := by
  apply NatTrans.ext
  funext T
  have hp := congrArg (fun a ↦ a.app T) (transferBaseChangePresheafIso_pullback f g F)
  change (baseChangePresheafPullback (pullback.snd f g) F).app T ≫
      ((transferBaseChangePresheafIso f g F).hom.app T ≫
        tr.transfer.app (op ((Over.map g).obj T.unop))) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ tr.transfer.app (op ((Over.map g).obj T.unop))) hp)

/-- 概要：底変換後の合成の成分は元の合成の同じ対象の成分（補題 3.2）。
方針：証明した自然変換の等式を評価する。
規約：指定射そのものの式。使われ方：値域関手での弱同値の移送。 -/
theorem BaseChangeTransfer.baseChange_composite_app (tr : BaseChangeTransfer f F) (T : Over Z) :
    (baseChangePresheafPullback (pullback.snd f g) F ≫
        (BaseChangeTransfer.baseChange f g F tr).transfer).app (op T) =
      (baseChangePresheafPullback f F ≫ tr.transfer).app (op ((Over.map g).obj T)) :=
  congrArg (fun a ↦ a.app (op T)) (BaseChangeTransfer.baseChange_composite f g F tr)

/-- 概要：元の合成の全成分の弱同値は任意の底変換に保たれる（補題 3.2）。
方針：指定合成の一致を値域関手で写す。
規約：値域関手の加法性は不要。使われ方：局所 rank から全底変換の実降下へ渡す。 -/
theorem BaseChangeTransfer.baseChange_composite_weak
    {W : Type*} [Category* W] [ModelCategory W] (U : V ⥤ W)
    (tr : BaseChangeTransfer f F)
    (hcomp : ∀ T : Over Y, weakEquivalences W
      (U.map ((baseChangePresheafPullback f F ≫ tr.transfer).app (op T))))
    (T : Over Z) : weakEquivalences W
      (U.map ((baseChangePresheafPullback (pullback.snd f g) F ≫
        (BaseChangeTransfer.baseChange f g F tr).transfer).app (op T))) := by
  rw [BaseChangeTransfer.baseChange_composite_app]
  exact hcomp _

end SerrePositivity.KST.Descent
