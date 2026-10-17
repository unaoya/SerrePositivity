module
public import SerrePositivity.DifferentialGraded.Derived.KFlatBimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionResolved

/-! # 第一中間圏の指定K-flatモデルと導来結合子のcoherence

## 概要
第一中間圏の指定K-flatモデルと導来結合子のcoherence。

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
  (T : Type s) [DGCategory A T] (F : DGFunctor A D C)
  (Q : RightKFlatBimoduleCategory A C E) (S : RightKFlatBimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "SR" => rightKFlatCompose A D E T S R
local notation "qR" => middleRestrictionComposeAugmentation A C D E T F Q.obj S.obj R.obj q

/-- 任意の指定増大について、第一中間比較は固定K-flat導来結合子と可換。 -/
lemma rightKFlatDerivedAssociator_middleRestriction :
    whiskerLeft L (rightKFlatDerivedAssociator A B D E T S R).hom ≫
      rightKFlatMiddleComparison A B C D T F QR SR qR =
    whiskerRight (rightKFlatMiddleComparison A B C D E F Q S q)
        (rightKFlatDerivedCompose A B E T R) ≫
      (rightKFlatDerivedAssociator A B C E T Q R).hom := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [rightKFlatMiddleComparison_base_app, rightKFlatMiddleComparison_base_app]
  have hαC := rightKFlatDerivedAssociator_base_app A B C E T Q R P
  rw [hαC]
  have hn := (rightKFlatDerivedAssociator A B D E T S R).hom.naturality
    ((middleLeftRestrictionDerivedIso A B C D F).inv.app P)
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  have hαD := rightKFlatDerivedAssociator_base_app A B D E T S R
    ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)
  erw [hαD]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hm := rightKFlatDerivedCompose_map_base A B E T R
    (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj q)
  rw [hm]
  have hs := congrArg ((bimoduleToDerived A B T).map)
    (associatorIso_middleRestriction_resolved A B C D E T F P Q.obj S.obj R.obj q)
  simp only [CategoryTheory.Functor.map_comp] at hs
  have h := congrArg (fun k => (rightKFlatDerivedCompose A B E T R).map
    ((rightKFlatDerivedCompose A B D E S).map
      ((middleLeftRestrictionDerivedIso A B C D F).inv.app P)) ≫ k) hs
  convert h using 1
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
