module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorSecondMiddleRestrictionInner

/-! # 第二中間制限と全導来結合子の入れ子側のモデルsquare

## 概要
第二中間制限と全導来結合子の入れ子側のモデルsquare。

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
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A E T) (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
  (hq : BimoduleCategory.quasiIso A D T q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "LQD" => Functor.obj
  (derivedBimoduleRestriction A C D C E (DGFunctor.id C) F) QT
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "eS" => middleRestrictionKFlatFactorIso A E D T F R S q hq
local notation "QS" => rightKFlatCompose A C D T LQ S
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "g" => middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q

/-- 第二中間比較は、入れ子合成の指定モデル表示を通して通常の解像度比較射の像になる。 -/
lemma derivedSecondMiddleRestriction_nested_model_square :
    (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT) ≫
      (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeNestedComparisonIso A B C D T hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom ≫
      rightKFlatDerivedMap A B C T (Q := QS) (Q' := QR) g := by
  have hi := derivedSecondMiddleRestriction_inner_model_square A C D E T F hT Q R S q hq
  let f : QS ⟶ QR := ⟨g⟩
  have hn := derivedBimoduleComposeKFlatIso_naturality A B C T hT f
  have h := congrArg (fun k => (derivedBimoduleComposeFunctor A B C T hT).map k) hi
  simp only [CategoryTheory.Functor.map_comp] at h
  have hh := congrArg (fun k => k ≫ (derivedBimoduleComposeKFlatIso A B C T hT QR).hom) h
  simp only [Category.assoc] at hh
  rw [hn] at hh
  convert hh using 1 <;>
    simp only [derivedBimoduleComposeNestedComparisonIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
