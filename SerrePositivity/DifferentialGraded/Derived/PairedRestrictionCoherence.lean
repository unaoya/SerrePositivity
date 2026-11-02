module
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.PairedRestrictionIdentification

/-! # 既存の両端導来制限の恒等・合成比較とモデル計算

## 概要
既存の両端導来制限の恒等・合成比較とモデル計算。

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
universe u v w z t s r
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

def pairedRestrictionIdDerivedPreIso :
    bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      bimoduleToDerived A B C ⋙ 𝟭 (DerivedBimoduleCategory A B C) :=
  (pairedRestrictionDerivedIso A B C B C (DGFunctor.id B) (DGFunctor.id C)).symm ≪≫
    Functor.isoWhiskerRight (BimoduleCategory.pairedRestrictionIdIso A B C)
      (bimoduleToDerived A B C)

/-- 既存の同時導来制限の恒等比較。 -/
def pairedRestrictionIdDerivedIso :
    derivedBimoduleRestriction A B C B C (DGFunctor.id B) (DGFunctor.id C) ≅
      𝟭 (DerivedBimoduleCategory A B C) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _ (pairedRestrictionIdDerivedPreIso A B C)

lemma pairedRestrictionIdDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionIdDerivedIso A B C).hom.app ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionIdDerivedPreIso A B C).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

variable (E : Type z) [DGCategory A E] [Small.{u} E]
  (L : Type t) [DGCategory A L] [Small.{u} L]
  (D : Type s) [DGCategory A D] [Small.{u} D]
  (K : Type r) [DGCategory A K] [Small.{u} K]
  (F : DGFunctor A D E) (G : DGFunctor A E B)
  (H : DGFunctor A K L) (I : DGFunctor A L C)

def pairedRestrictionCompDerivedPreIso :
    bimoduleToDerived A B C ⋙
        (derivedBimoduleRestriction A E L B C G I ⋙
          derivedBimoduleRestriction A D K E L F H) ≅
      bimoduleToDerived A B C ⋙
        derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  Functor.isoWhiskerRight (pairedRestrictionDerivedIso A B C E L G I).symm
      (derivedBimoduleRestriction A D K E L F H) ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.pairedRestrictionFunctor A B C E L G I)
      (pairedRestrictionDerivedIso A E L D K F H).symm ≪≫
    Functor.isoWhiskerRight
      (BimoduleCategory.pairedRestrictionCompIso A B C E L D K F G H I)
      (bimoduleToDerived A D K) ≪≫
    pairedRestrictionDerivedIso A B C D K (F.comp G) (H.comp I)

/-- 二つの既存同時導来制限の合成を、合成dg関手による既存制限へ送る。 -/
def pairedRestrictionCompDerivedIso :
    derivedBimoduleRestriction A E L B C G I ⋙ derivedBimoduleRestriction A D K E L F H ≅
      derivedBimoduleRestriction A D K B C (F.comp G) (H.comp I) :=
  bimoduleDerivedIsoOfPrecomp A B C _ _
    (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I)

lemma pairedRestrictionCompDerivedIso_hom_app (P : BimoduleCategory A B C) :
    (pairedRestrictionCompDerivedIso A B C E L D K F G H I).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (pairedRestrictionCompDerivedPreIso A B C E L D K F G H I).hom.app P :=
  bimoduleDerivedIsoOfPrecomp_hom_app A B C _ _ _ P

end SerrePositivity.DifferentialGraded
