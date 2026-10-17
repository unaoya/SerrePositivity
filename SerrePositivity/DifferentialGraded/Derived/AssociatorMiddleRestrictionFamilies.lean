module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionModel

/-! # 第一中間制限と全導来結合子の両経路の三変数自然性

## 概要
第一中間制限と全導来結合子の両経路の三変数自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)

local notation "X" => DerivedBimoduleCategory A B C
local notation "XD" => DerivedBimoduleCategory A B D
local notation "Y" => DerivedBimoduleCategory A C E
local notation "YD" => DerivedBimoduleCategory A D E
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A B T
local notation "BE" => DerivedBimoduleCategory A B E
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RQ" => derivedBimoduleRestriction A D E C E F (DGFunctor.id E)
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "HR" => derivedBimoduleComposeFunctor A C E T hT
local notation "HBR" => derivedBimoduleComposeFunctor A B E T hT
local notation "preQ" => Functor.obj (whiskeringLeft Y YD (XD ⥤ W)) RQ
local notation "preP" => Functor.obj (whiskeringRight Y (XD ⥤ W) (X ⥤ W))
  (Functor.obj (whiskeringLeft X XD W) L)

/-- 最初の中間圏を制限した後の二段階合成の、全三変数のsource関手族。 -/
def middleRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorSource A B D E T hE hT ⋙ preQ ⋙ preP

/-- 制限後の結合子、内側右比較、中間比較を続ける経路。 -/
def middleRestrictionAssociatorLeftPath :
    middleRestrictionAssociatorSource A B C D E T F hE hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerRight (derivedBimoduleAssociatorIso A B D E T hE hT).hom (preQ ⋙ preP) ≫
    whiskerRight (derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom
      ((whiskeringRight Y (DerivedBimoduleCategory A D T) (XD ⥤ W)).obj HD ⋙ preP) ≫
    whiskerLeft HR ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).map
      (derivedMiddleRestrictionNatTrans A B C D T F hT))

/-- 中間比較を後因子との合成へ送った後、元の結合子を続ける経路。 -/
def middleRestrictionAssociatorRightPath :
    middleRestrictionAssociatorSource A B C D E T F hE hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerLeft (HBR ⋙ whiskeringRight X BE W)
      ((whiskeringLeft Y (X ⥤ BE) (X ⥤ W)).map
        (derivedMiddleRestrictionNatTrans A B C D E F hE)) ≫
    (derivedBimoduleAssociatorIso A B C E T hE hT).hom

lemma middleRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((middleRestrictionAssociatorLeftPath A B C D E T F hE hT).app R).app Q =
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT ((RQ).obj Q) R).hom ≫
      whiskerLeft L ((HD).map
        (((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app R).app Q)) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app (((HR).obj R).obj Q) := rfl

lemma middleRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((middleRestrictionAssociatorRightPath A B C D E T F hE hT).app R).app Q =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q) ((HBR).obj R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
