module

public import SerrePositivity.KST.Descent.TransferBaseChangeGeometry

/-!
# 自然な transfer と rank 公式の実際の底変換

## 概要
全ての基底上の対象で自然な transfer を任意の基底変更へ制限し、同じ rank 公式を証明する。

## 方針
第一射影を保つ二重引き戻しの自然同型を元の前層で写し、元の transfer 自然変換を前合成する。

## 規約
底変換後の transfer の存在や rank 公式を追加仮定にしない。元の指定 pullback との式を検査する。

## 使われ方
論文 補題 3.2 の有限平坦 transfer の各 Čech 段・各 chart 上への制限。
-/

@[expose] public section

noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {V : Type w} [Category.{t} V] {X Y Z : C}
  (f : X ⟶ Y) (g : Z ⟶ Y) (F : Cᵒᵖ ⥤ V)

/-- 概要：底変換した射の前層は元の底変換前層の制限に自然同型（補題 3.2）。
方針：指定第一射影を保つ二重引き戻し同型を元の反変前層で写す。
規約：全基底上の射に自然。使われ方：元の transfer を底変換へ制限する始域の比較。 -/
def transferBaseChangePresheafIso :
    baseChangedPresheaf (pullback.snd f g) F ≅ (Over.map g).op ⋙ baseChangedPresheaf f F :=
  Functor.isoWhiskerRight (NatIso.op (transferBaseChangeGeometryIso f g)) F

/-- 概要：底変換後の自然な pullback は指定前層同型で元の制限に一致（補題 3.2）。
方針：元の pullback の成分公式と、二重引き戻し同型の第一射影公式を使う。
規約：指定射そのものの自然変換の等式。使われ方：底変換後の rank 公式。 -/
theorem transferBaseChangePresheafIso_pullback :
    baseChangePresheafPullback (pullback.snd f g) F ≫
        (transferBaseChangePresheafIso f g F).hom =
      Functor.whiskerLeft (Over.map g).op (baseChangePresheafPullback f F) := by
  apply NatTrans.ext
  funext T
  change (baseChangePresheafPullback (pullback.snd f g) F).app T ≫
      F.map (transferBaseChangeStageIso f g T.unop).hom.op =
    (baseChangePresheafPullback f F).app (op ((Over.map g).obj T.unop))
  rw [baseChangePresheafPullback_app, baseChangePresheafPullback_app]
  exact (F.map_comp (pullback.fst T.unop.hom (pullback.snd f g)).op
    (transferBaseChangeStageIso f g T.unop).hom.op).symm.trans
    (congrArg F.map (congrArg Quiver.Hom.op (transferBaseChangeStageIso_hom_fst f g T.unop)))

/-- 概要：全基底上で自然な transfer を任意の底変換へ実際に制限（補題 3.2）。
方針：指定前層同型の後に元の transfer の前合成を取る。
規約：元の前層と元の transfer を使用。使われ方：各 Čech 段の transfer による実降下。 -/
def BaseChangeTransfer.baseChange (tr : BaseChangeTransfer f F) :
    BaseChangeTransfer (pullback.snd f g) F where
  transfer := (transferBaseChangePresheafIso f g F).hom ≫
    Functor.whiskerLeft (Over.map g).op tr.transfer

variable [Preadditive V] [Linear ℚ V]

/-- 概要：自然な transfer の rank 公式は同じ rank で任意の底変換へ移る（補題 3.2）。
方針：指定 pullback の比較式で元の rank 公式の制限へ帰着する。
規約：正値性は不要で任意の自然数 rank の式を保つ。使われ方：各 Čech 段と局所 chart の降下。 -/
theorem BaseChangeTransfer.baseChange_rank_identity (tr : BaseChangeTransfer f F)
    (rank : ℕ)
    (hrank : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    baseChangePresheafPullback (pullback.snd f g) F ≫
        (BaseChangeTransfer.baseChange f g F tr).transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Z) F) := by
  apply NatTrans.ext
  funext T
  have hp := congrArg (fun a ↦ a.app T) (transferBaseChangePresheafIso_pullback f g F)
  have hr := congrArg (fun a ↦ a.app (op ((Over.map g).obj T.unop))) hrank
  change (baseChangePresheafPullback (pullback.snd f g) F).app T ≫
      ((transferBaseChangePresheafIso f g F).hom.app T ≫
        tr.transfer.app (op ((Over.map g).obj T.unop))) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ tr.transfer.app (op ((Over.map g).obj T.unop))) hp).trans hr)

end SerrePositivity.KST.Descent
