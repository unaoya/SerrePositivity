module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionFamilies

/-! # 全導来三因子に対する第一中間制限と結合子のcoherence

## 概要
全導来三因子に対する第一中間制限と結合子のcoherence。

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

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RQ" => derivedBimoduleRestriction A D E C E F (DGFunctor.id E)

/-- 指定モデル上の一致を後二つの全導来変数へ持ち上げた、両経路の一致。 -/
lemma middleRestrictionAssociatorPaths_eq :
    middleRestrictionAssociatorLeftPath A B C D E T F hE hT =
      middleRestrictionAssociatorRightPath A B C D E T F hE hT := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [middleRestrictionAssociatorLeftPath_app, middleRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_middleRestriction_rightKFlat A B C D E T F hE hT Q R

/-- 任意の導来三因子で、第一中間圏の全導来比較は実際の全導来結合子と可換。 -/
lemma derivedBimoduleAssociator_middleRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT ((RQ).obj Q) R).hom ≫
      whiskerLeft L ((derivedBimoduleComposeFunctor A B D T hT).map
        (((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app R).app Q)) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app
        (((derivedBimoduleComposeFunctor A C E T hT).obj R).obj Q) =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q)
        ((derivedBimoduleComposeFunctor A B E T hT).obj R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (middleRestrictionAssociatorPaths_eq A B C D E T F hE hT) R) Q
  simpa only [middleRestrictionAssociatorLeftPath_app,
    middleRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
