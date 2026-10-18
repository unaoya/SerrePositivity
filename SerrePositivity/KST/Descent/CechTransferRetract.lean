module

public import SerrePositivity.KST.Descent.PresheafAugmentation
public import SerrePositivity.KST.Descent.SplitCech

/-!
# 実際の Čech 増強比較に対する transfer の retract

## 概要
元の前層の Čech 増強と、実際の底変換後の前層の Čech 増強の間に retract を構成する。

## 方針
Čech nerve を Over Y の図式にし、前層の自然な transfer と局所 rank 公式を制限する。

## 規約
Čech の各次数と増強先の値を同時に保持する。Tot は取らず、π_* との交換も仮定しない。

## 使われ方
論文 補題 3.2 の有限平坦 transfer による降下比較の retract の幾何入力。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {V : Type w} [Category.{t} V] {W Y : C} (cover : W ⟶ Y)

/-- 概要：実際の Čech nerve を同じ基底上の図式にする（論文 補題 3.2）。
方針：指定増強の各成分を構造射として Over へ持ち上げる。
規約：面射・退化射は元の Čech nerve の射。
使われ方：全次数に共通する transfer 自然変換の制限。 -/
noncomputable def cechOverDiagram : SimplexCategoryᵒᵖ ⥤ Over Y :=
  Over.lift (Arrow.mk cover).cechNerve (Arrow.mk cover).augmentedCechNerve.hom

/-- 概要：元の前層の実際の Čech 増強比較（論文 補題 3.2）。
方針：Over の Čech 図式の構造射を元の前層で引き戻す。
規約：増強先は元の基底 Y での値。
使われ方：Tot を適用する前の指定比較。 -/
noncomputable def cechPresheafAugmentation (F : Cᵒᵖ ⥤ V) :
    (Functor.const (SimplexCategoryᵒᵖ)ᵒᵖ).obj (F.obj (op Y)) ⟶
      (cechOverDiagram cover).op ⋙ overPresheaf (Y := Y) F :=
  presheafDiagramAugmentation (cechOverDiagram cover) (overPresheaf (Y := Y) F)

/-- 概要：指定 Čech 増強の成分は元の幾何的増強の引き戻し（論文 補題 3.2）。
方針：Over の構造射の定義を成分で検査する。
規約：対象ごとの任意の比較射ではない。
使われ方：前層の実降下の指定比較との一致。 -/
theorem cechPresheafAugmentation_app (F : Cᵒᵖ ⥤ V) (n : SimplexCategoryᵒᵖ) :
    (cechPresheafAugmentation cover F).app (op n) =
      F.map ((Arrow.mk cover).augmentedCechNerve.hom.app n).op := rfl

/-- 概要：底変換後の前層の実際の Čech 増強比較（論文 補題 3.2）。
方針：同じ Čech 図式へ実際の基底変更後の前層を制限する。
規約：pullback の自然変換と同じ基底変更関手を使う。
使われ方：transfer retract の比較先。 -/
noncomputable def cechBaseChangedAugmentation {X : C} (f : X ⟶ Y) (F : Cᵒᵖ ⥤ V) :=
  presheafDiagramAugmentation (cechOverDiagram cover) (baseChangedPresheaf f F)

variable [Preadditive V] [Linear ℚ V]

/-- 概要：実際の Čech 増強比較は transfer により底変換後の比較の retract（論文 補題 3.2）。
方針：全ての基底変更に自然な transfer を Čech 図式に制限し、局所 rank で正規化する。
規約：有限平坦 transfer の存在・局所 rank 公式は明示した入力。Tot の同値は結論しない。
使われ方：実際の Tot 関手による比較に渡す矢の圏の retract。 -/
noncomputable def BaseChangeTransfer.cechAugmentationRetract {X : C} {f : X ⟶ Y}
    {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    RetractArrow (cechPresheafAugmentation cover F) (cechBaseChangedAugmentation cover f F) :=
  BaseChangeTransfer.augmentationRetract (cechOverDiagram cover) tr rank positive rank_identity

/-- 概要：任意の実際の図式関手で写しても Čech 比較の retract は保たれる（論文 補題 3.2）。
方針：矢の圏の retract の関手による保存を適用する。
規約：ここで関手が Tot であることやその実構成を仮定しない。
使われ方：L9 の実際の Tot が供給された後に、その比較射へ移す。 -/
noncomputable def BaseChangeTransfer.mapCechAugmentationRetract
    {D : Type*} [Category* D]
    (total : ((SimplexCategoryᵒᵖ)ᵒᵖ ⥤ V) ⥤ D)
    {X : C} {f : X ⟶ Y} {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F)) :
    RetractArrow (total.map (cechPresheafAugmentation cover F))
      (total.map (cechBaseChangedAugmentation cover f F)) :=
  (BaseChangeTransfer.cechAugmentationRetract cover tr rank positive rank_identity).map total

/-- 概要：実際の Čech transfer retract による全次数比較の移行（論文 補題 3.2）。
方針：指定 Čech 比較の retract を実際の図式関手で写し、全次数同型の retract 安定性を使う。
規約：観測関手と図式関手は明示した引数で、L9 の Tot・π_* の実構成の接続は別工程。
使われ方：底変換後の分裂降下から元の増強比較へ戻す最終的な形式的操作。 -/
theorem BaseChangeTransfer.piCechComparison_of_transfer
    {D : Type*} [Category* D]
    (total : ((SimplexCategoryᵒᵖ)ᵒᵖ ⥤ V) ⥤ D)
    (observation : ℤ → D ⥤ ModuleCat ℚ)
    {X : C} {f : X ⟶ Y} {F : Cᵒᵖ ⥤ V} (tr : BaseChangeTransfer f F)
    (rank : ℕ) (positive : 0 < rank)
    (rank_identity : baseChangePresheafPullback f F ≫ tr.transfer =
      (rank : ℚ) • 𝟙 (overPresheaf (Y := Y) F))
    (baseChanged : piIsomorphisms observation (total.map (cechBaseChangedAugmentation cover f F))) :
    piIsomorphisms observation (total.map (cechPresheafAugmentation cover F)) :=
  piIsomorphisms_of_retract observation
    (BaseChangeTransfer.mapCechAugmentationRetract cover total tr rank positive rank_identity)
    baseChanged

end SerrePositivity.KST.Descent
