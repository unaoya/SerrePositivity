module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeftRestrictionModel

/-! # 外側左制限と結合子の両経路を三変数の全導来関手族へ束ねる

## 概要
外側左制限と結合子の両経路を三変数の全導来関手族へ束ねる。

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
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)

local notation "X" => DerivedBimoduleCategory A B C
local notation "Y" => DerivedBimoduleCategory A C E
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A B D
local notation "V" => DerivedBimoduleCategory A B T
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "LC" => derivedBimoduleRestriction A C D C T (DGFunctor.id C) G
local notation "LE" => derivedBimoduleRestriction A E D E T (DGFunctor.id E) G
local notation "HQ" => derivedBimoduleComposeFunctor A B C E hE
local notation "HD" => derivedBimoduleComposeFunctor A B C D hD
local notation "HR" => derivedBimoduleComposeFunctor A C E T hT

/-- 後因子を左制限してから二段階合成する、全三因子のsource関手族。 -/
def leftRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  LE ⋙ derivedBimoduleAssociatorSource A B C E D hE hD

/-- 全三因子の合成後に出力を左制限する、両経路共通のtarget関手族。 -/
def leftRestrictionAssociatorTarget : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorTarget A B C E T hT ⋙
    (whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj L)

/-- 後因子を左制限した全導来結合子のtarget。 -/
def leftRestrictionAssociatorAfterAssociator : Z ⥤ Y ⥤ X ⥤ W :=
  LE ⋙ derivedBimoduleAssociatorTarget A B C E D hD

/-- 内側の左制限比較を通した後、外側比較を適用する前の関手族。 -/
def leftRestrictionAssociatorAfterInner : Z ⥤ Y ⥤ X ⥤ W :=
  HR ⋙ (whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).obj (LC ⋙ HD)

/-- 元の二段階合成を出力で左制限した、右側経路の中間関手族。 -/
def leftRestrictionAssociatorRightMiddle : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorSource A B C E T hE hT ⋙
    (whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj L)

/-- 結合子、内側比較、外側比較を続ける、全後二因子にも自然な経路。 -/
def leftRestrictionAssociatorLeftPath :
    leftRestrictionAssociatorSource A B C E T D G hE hD ⟶
      leftRestrictionAssociatorTarget A B C E T D G hT :=
  whiskerLeft LE (derivedBimoduleAssociatorIso A B C E D hE hD).hom ≫
    whiskerRight (derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv
      ((whiskeringRight Y (DerivedBimoduleCategory A C D) (X ⥤ W)).obj HD) ≫
    whiskerLeft HR ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).map
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv)

/-- 二段階合成の外側比較と元の結合子を続ける、全後二因子にも自然な経路。 -/
def leftRestrictionAssociatorRightPath :
    leftRestrictionAssociatorSource A B C E T D G hE hD ⟶
      leftRestrictionAssociatorTarget A B C E T D G hT :=
  whiskerRight (derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv
      (whiskeringRight X (DerivedBimoduleCategory A B E) W ⋙
        (whiskeringLeft Y (X ⥤ DerivedBimoduleCategory A B E) (X ⥤ W)).obj HQ) ≫
    whiskerRight (derivedBimoduleAssociatorIso A B C E T hE hT).hom
      ((whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj L))

/-- 左経路の成分は、実際の既存比較三つの合成になる。 -/
lemma leftRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((leftRestrictionAssociatorLeftPath A B C E T D G hE hT hD).app R).app Q =
    (derivedBimoduleAssociator A B C E D hE hD Q ((LE).obj R)).hom ≫
      (HD).map (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app R).app Q) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app
        (((HR).obj R).obj Q) := rfl

/-- 右経路の成分も、実際の既存比較のwhiskerの合成になる。 -/
lemma leftRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((leftRestrictionAssociatorRightPath A B C E T D G hE hT hD).app R).app Q =
    whiskerLeft ((HQ).obj Q)
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom L := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
