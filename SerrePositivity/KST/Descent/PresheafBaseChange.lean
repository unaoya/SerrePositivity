module

public import SerrePositivity.KST.Descent.DiagramTransfer
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# 実際の底変換からの前層の pullback 自然変換

## 概要
固定した射 f と元の前層から、全ての基底変更に自然な pullback を構成する。

## 方針
Over の底変換随伴の余単位を反変前層で写す。

## 規約
transfer の存在や射影公式は主張しない。局所 rank 公式は明示した追加データ。

## 使われ方
論文 補題 3.2 の有限平坦 transfer による前層そのものの retract。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {V : Type w} [Category.{t} V] {X Y : C} (f : X ⟶ Y)

/-- 概要：基底変更後の対象を同じ基底 Y 上へ戻す関手（論文 補題 3.2）。
方針：Over の pullback と構造射の合成を使う。
規約：Z → Y を Z ×_Y X → Y に写す。
使われ方：元の前層と底変換後の前層の比較。 -/
noncomputable def overBaseChange : Over Y ⥤ Over Y := Over.pullback f ⋙ Over.map f

/-- 概要：元の前層を基底 Y 上の全ての対象で評価する（論文 補題 3.2）。
方針：Over の忘却を元の反変前層に前合成する。
規約：前層を別の任意の前層に交換しない。
使われ方：transfer の自然性の定義域。 -/
def overPresheaf (F : Cᵒᵖ ⥤ V) : (Over Y)ᵒᵖ ⥤ V := (Over.forget Y).op ⋙ F

/-- 概要：実際の基底変更後の前層（論文 補題 3.2）。
方針：元の Over 上の前層を基底変更関手に前合成する。
規約：全ての基底変更の射についての関手性を保持する。
使われ方：前層としての transfer の始域。 -/
noncomputable def baseChangedPresheaf (F : Cᵒᵖ ⥤ V) : (Over Y)ᵒᵖ ⥤ V :=
  (overBaseChange f).op ⋙ overPresheaf (Y := Y) F

/-- 概要：実際の底変換から元の前層の自然な pullback（論文 補題 3.2）。
方針：Over の随伴の余単位を反対圏で写し、元の前層を適用する。
規約：対象ごとに任意の写像を選ぶのではない。
使われ方：有限平坦 transfer の正規化による retract の inclusion。 -/
noncomputable def baseChangePresheafPullback (F : Cᵒᵖ ⥤ V) :
    overPresheaf (Y := Y) F ⟶ baseChangedPresheaf f F :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (NatTrans.op (Over.mapPullbackAdj f).counit)
      (overPresheaf (Y := Y) F)

/-- 概要：自然な pullback の成分は実際の第一射影の引き戻し（論文 補題 3.2）。
方針：余単位の定義を成分で検査する。
規約：底変換は Z ×_Y X とし、第一射影は Z への射。
使われ方：既存の幾何射の比較と transfer の局所公式の一致。 -/
theorem baseChangePresheafPullback_app (F : Cᵒᵖ ⥤ V) (Z : Over Y) :
    (baseChangePresheafPullback f F).app (op Z) = F.map (pullback.fst Z.hom f).op := by
  change 𝟙 _ ≫ F.map ((𝟙 _ ≫ pullback.fst Z.hom f).op) = _
  exact (Category.id_comp _).trans
    (congrArg F.map (congrArg Quiver.Hom.op (Category.id_comp _)))

/-- 概要：基底自身を底変換した対象は元の始域と同型（論文 補題 3.2）。
方針：恒等射を第一の辺とする引き戻しの第二射影を使う。
規約：同じ Over Y の構造射を保持する。
使われ方：Čech 増強先の底変換後の値を元の始域の値と比較する。 -/
noncomputable def overBaseChangeBaseIso :
    (overBaseChange f).obj (Over.mk (𝟙 Y)) ≅ Over.mk f :=
  Over.isoMk
    { hom := pullback.snd (𝟙 Y) f
      inv := pullback.lift f (𝟙 X) (by simp)
      hom_inv_id := by
        apply pullback.hom_ext
        · exact (Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) (pullback.lift_fst f (𝟙 X) (by simp))).trans
              ((pullback.condition.symm.trans (Category.comp_id _)).trans
                (Category.id_comp _).symm))
        · exact (Category.assoc _ _ _).trans
            ((congrArg (_ ≫ ·) (pullback.lift_snd f (𝟙 X) (by simp))).trans
              ((Category.comp_id _).trans (Category.id_comp _).symm))
      inv_hom_id := pullback.lift_snd f (𝟙 X) (by simp) } (by rfl)

/-- 概要：基底での自然な pullback は元の射の引き戻しと標準同型で一致（論文 補題 3.2）。
方針：引き戻しの二射影の可換性に元の前層を適用する。
規約：増強先の比較射そのものを保持する。
使われ方：実際の Čech 降下の増強先と transfer 図式の接続。 -/
theorem baseChangePresheafPullback_at_base (F : Cᵒᵖ ⥤ V) :
    (baseChangePresheafPullback f F).app (op (Over.mk (𝟙 Y))) =
      F.map f.op ≫ F.map (overBaseChangeBaseIso f).hom.left.op := by
  have h : (overBaseChangeBaseIso f).hom.left ≫ f = pullback.fst (𝟙 Y) f :=
    pullback.condition.symm.trans (Category.comp_id _)
  exact (baseChangePresheafPullback_app f F _).trans
    ((congrArg F.map (congrArg Quiver.Hom.op h)).symm.trans
      (F.map_comp _ _))

/-- 概要：前層に関する基底変更 transfer の自然変換のデータ（論文 補題 3.2、公理 (4) の一部）。
方針：全ての基底変更とその射に自然な一つの逆方向の自然変換を保持する。
規約：幾何的な有限平坦性や射影公式の検証は含めない。
使われ方：K の実際の transfer を接続し、局所 rank 公式で retract を導く。 -/
structure BaseChangeTransfer (F : Cᵒᵖ ⥤ V) where
  /-- 概要：基底変更後から元への transfer（論文 補題 3.2）。
  方針：Over Y 全体の自然変換として保持する。
  規約：対象ごとの写像だけには弱めない。
  使われ方：局所自明化後の正規化。 -/
  transfer : baseChangedPresheaf f F ⟶ overPresheaf (Y := Y) F

variable [Preadditive V] [Linear ℚ V]

/-- 概要：局所 rank 公式を満たす実際の pullback と transfer の前層 retract（論文 補題 3.2）。
方針：正の rank で transfer を割り、自然変換としての片側逆を構成する。
規約：rank 公式は局所自明化後に供給すべき条件で、大域的な定数 rank 公式ではない。
使われ方：Čech の増強を含む図式へ適用する前の前層そのものの retract。 -/
noncomputable def BaseChangeTransfer.retract {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    Retract (overPresheaf (Y := Y) F) (baseChangedPresheaf f F) :=
  rankTransferRetract rank positive (baseChangePresheafPullback f F) tr.transfer rank_identity

end SerrePositivity.KST.Descent
