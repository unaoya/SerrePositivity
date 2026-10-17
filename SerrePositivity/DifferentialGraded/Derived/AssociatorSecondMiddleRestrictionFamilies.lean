module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionModel

/-! # 第二中間制限と全導来結合子の両経路の三変数自然性

## 概要
第二中間制限と全導来結合子の両経路の三変数自然性。

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
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D) (hT : localHomKFlat A T)

local notation "X" => DerivedBimoduleCategory A B C
local notation "Y" => DerivedBimoduleCategory A C E
local notation "YD" => DerivedBimoduleCategory A C D
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A B T
local notation "BD" => DerivedBimoduleCategory A B D
local notation "BE" => DerivedBimoduleCategory A B E
local notation "LQ" => derivedBimoduleRestriction A C D C E (DGFunctor.id C) F
local notation "RR" => derivedBimoduleRestriction A D T E T F (DGFunctor.id T)
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "HC" => derivedBimoduleComposeFunctor A B C T hT
local notation "HQ" => derivedBimoduleComposeFunctor A B C E hE
local notation "preQ" => Functor.obj (whiskeringLeft Y YD (X ⥤ W)) LQ

/-- 後二因子の間の圏を制限した二段階合成を束ねるsource関手族。 -/
def secondMiddleRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  RR ⋙ derivedBimoduleAssociatorSource A B C D T hD hT ⋙ preQ

/-- 外側左比較、中間比較、元の結合子を続ける全三変数の経路。 -/
def secondMiddleRestrictionAssociatorLeftPath :
    secondMiddleRestrictionAssociatorSource A B C D E T F hD hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerLeft (RR ⋙ HD ⋙ whiskeringRight X BD W)
      ((whiskeringLeft Y (X ⥤ BD) (X ⥤ W)).map
        (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv) ≫
    whiskerRight (derivedMiddleRestrictionNatTrans A B E D T F hT)
      (whiskeringRight X BE W ⋙ (whiskeringLeft Y (X ⥤ BE) (X ⥤ W)).obj HQ) ≫
    (derivedBimoduleAssociatorIso A B C E T hE hT).hom

/-- 制限後の結合子と内側の中間比較を続ける全三変数の経路。 -/
def secondMiddleRestrictionAssociatorRightPath :
    secondMiddleRestrictionAssociatorSource A B C D E T F hD hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerRight (whiskerLeft RR (derivedBimoduleAssociatorIso A B C D T hD hT).hom) preQ ≫
    whiskerRight (derivedMiddleRestrictionNatTrans A C E D T F hT)
      ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).obj HC)

lemma secondMiddleRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((secondMiddleRestrictionAssociatorLeftPath A B C D E T F hE hD hT).app R).app Q =
    whiskerRight ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app Q)
        ((HD).obj ((RR).obj R)) ≫
      whiskerLeft ((HQ).obj Q) ((derivedMiddleRestrictionNatTrans A B E D T F hT).app R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom := rfl

lemma secondMiddleRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((secondMiddleRestrictionAssociatorRightPath A B C D E T F hD hT).app R).app Q =
    (derivedBimoduleAssociator A B C D T hD hT ((LQ).obj Q) ((RR).obj R)).hom ≫
      (HC).map (((derivedMiddleRestrictionNatTrans A C E D T F hT).app R).app Q) := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
