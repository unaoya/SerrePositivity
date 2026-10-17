module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionFamilies

/-! # 全導来三因子に対する結合子と外側右制限のcoherence

## 概要
全導来三因子に対する結合子と外側右制限のcoherence。

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

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)

/-- 指定K-flatモデル上の一致から全後二因子に自然な経路の一致を得る。 -/
lemma rightRestrictionAssociatorPaths_eq :
    rightRestrictionAssociatorLeftPath A B D C E T F hE hT =
      rightRestrictionAssociatorRightPath A B D C E T F hE hT := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [rightRestrictionAssociatorLeftPath_app, rightRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_rightRestriction_rightKFlat A B D C E T F hE hT Q R

/-- 任意の導来三因子について、外側右制限が実際の全導来結合子を保つ。 -/
lemma derivedBimoduleAssociator_rightRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT Q R).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app
        (((derivedBimoduleComposeFunctor A C E T hT).obj R).obj Q) =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app Q)
        ((derivedBimoduleComposeFunctor A D E T hT).obj R) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom RO := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (rightRestrictionAssociatorPaths_eq A B D C E T F hE hT) R) Q
  simpa only [rightRestrictionAssociatorLeftPath_app,
    rightRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
