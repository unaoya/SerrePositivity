module
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification
public import SerrePositivity.DifferentialGraded.Derived.BimoduleLeftRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull

/-! # 合成の両端のdg圏の制限と全導来bimodule合成の比較

## 概要
合成の両端のdg圏の制限と全導来bimodule合成の比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
U12e-general（中断）の一部。R1〜R7への足場として保持する。収録された個別宣言の証明済み範囲と、一般経路全体の未受入を区別する。
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
  (K : Type s) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D B) (H : DGFunctor A K E)
  (hE : localHomKFlat A E) (hK : localHomKFlat A K)

/-- 両因子の外側の作用をそれぞれ制限してから合成する既存導来関手族。 -/
def endpointRestrictionDerivedSource : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleRestriction A C K C E (DGFunctor.id C) H ⋙
    derivedBimoduleComposeFunctor A D C K hK ⋙
      (whiskeringLeft _ _ _).obj (derivedBimoduleRestriction A D C B C F (DGFunctor.id C))

/-- 合成後の両端を、既存の同時導来制限で制限する関手族。 -/
def endpointRestrictionDerivedTarget : DerivedBimoduleCategory A C E ⥤
    (DerivedBimoduleCategory A B C ⥤ DerivedBimoduleCategory A D K) :=
  derivedBimoduleComposeFunctor A B C E hE ⋙
    (whiskeringRight _ _ _).obj (derivedBimoduleRestriction A D K B E F H)

/-- 外側左右の既存比較と両端制限の表示同型から作る、全導来合成比較。 -/
def derivedBimoduleComposeEndpointRestrictionIso :
    endpointRestrictionDerivedSource A B D C E K F H hK ≅
      endpointRestrictionDerivedTarget A B D C E K F H hE :=
  Functor.isoWhiskerLeft (derivedBimoduleRestriction A C K C E (DGFunctor.id C) H)
      (derivedBimoduleComposeRightRestrictionIso A B D C K F hK) ≪≫
    Functor.isoWhiskerRight
      (derivedBimoduleComposeLeftRestrictionIso A B C E K H hE hK).symm
      ((whiskeringRight _ _ _).obj
        (derivedBimoduleRestriction A D K B K F (DGFunctor.id K))) ≪≫
    Functor.isoWhiskerLeft (derivedBimoduleComposeFunctor A B C E hE)
      ((whiskeringRight _ _ _).mapIso (pairedRestrictionPartialDerivedIso A B E D K F H))

end SerrePositivity.DifferentialGraded.BimoduleTensor
