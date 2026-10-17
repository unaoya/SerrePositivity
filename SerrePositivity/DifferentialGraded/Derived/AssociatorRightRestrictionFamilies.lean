module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionModel

/-! # 外側右制限と結合子の両経路の全三変数自然性

## 概要
外側右制限と結合子の両経路の全三変数自然性。

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
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)

local notation "X" => DerivedBimoduleCategory A B C
local notation "XD" => DerivedBimoduleCategory A D C
local notation "Y" => DerivedBimoduleCategory A C E
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A D T
local notation "V" => DerivedBimoduleCategory A B T
local notation "DE" => DerivedBimoduleCategory A D E
local notation "BE" => DerivedBimoduleCategory A B E
local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "HBQ" => derivedBimoduleComposeFunctor A B C E hE
local notation "HDR" => derivedBimoduleComposeFunctor A D E T hT
local notation "HR" => derivedBimoduleComposeFunctor A C E T hT
local notation "βQ" => Iso.hom (derivedBimoduleComposeRightRestrictionIso A B D C E F hE)
local notation "βR" => Iso.hom (derivedBimoduleComposeRightRestrictionIso A B D E T F hT)

/-- 前因子を右制限してから二段階合成する全三変数の関手族。 -/
def rightRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorSource A D C E T hE hT ⋙
    (whiskeringRight Y (XD ⥤ W) (X ⥤ W)).obj ((whiskeringLeft X XD W).obj RI)

/-- 三因子の合成後に外側右制限を適用する、両経路共通の関手族。 -/
def rightRestrictionAssociatorTarget : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorTarget A B C E T hT ⋙
    (whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj RO)

/-- 全導来結合子と入れ子合成の右制限比較を続ける経路。 -/
def rightRestrictionAssociatorLeftPath :
    rightRestrictionAssociatorSource A B D C E T F hE hT ⟶
      rightRestrictionAssociatorTarget A B D C E T F hT :=
  whiskerRight (derivedBimoduleAssociatorIso A D C E T hE hT).hom
      ((whiskeringRight Y (XD ⥤ W) (X ⥤ W)).obj ((whiskeringLeft X XD W).obj RI)) ≫
    whiskerLeft HR ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).map
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom)

/-- 二段階の右制限比較と元の全導来結合子を続ける経路。 -/
def rightRestrictionAssociatorRightPath :
    rightRestrictionAssociatorSource A B D C E T F hE hT ⟶
      rightRestrictionAssociatorTarget A B D C E T F hT :=
  whiskerLeft (HDR ⋙ whiskeringRight X DE W)
      ((whiskeringLeft Y (X ⥤ DE) (X ⥤ W)).map βQ) ≫
    whiskerRight βR (whiskeringRight X BE W ⋙
      (whiskeringLeft Y (X ⥤ BE) (X ⥤ W)).obj HBQ) ≫
    whiskerRight (derivedBimoduleAssociatorIso A B C E T hE hT).hom
      ((whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj RO))

lemma rightRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((rightRestrictionAssociatorLeftPath A B D C E T F hE hT).app R).app Q =
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT Q R).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app
        (((HR).obj R).obj Q) := rfl

lemma rightRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((rightRestrictionAssociatorRightPath A B D C E T F hE hT).app R).app Q =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app Q)
        ((HDR).obj R) ≫
      whiskerLeft ((HBQ).obj Q)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom RO := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
