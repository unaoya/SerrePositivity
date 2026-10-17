module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorRightRestrictionPresentation

/-! # 外側右制限の全導来比較と入れ子合成の表示

## 概要
外側右制限の全導来比較と入れ子合成の表示。

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
  (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT

/-- 後二因子の入れ子表示と全導来外側右比較は、固定K-flat比較のsquareをなす。 -/
lemma derivedRightRestriction_nested_model_square :
    (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app U ≫
      whiskerRight (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom RO =
    whiskerLeft RI (derivedBimoduleComposeNestedComparisonIso A D C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C T F
        (rightKFlatCompose A C E T Q R)).hom := by
  let i := derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have hn := (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.naturality i.hom
  have hm := derivedBimoduleComposeRightRestrictionIso_model_calculation A B D C T F hT
    (rightKFlatCompose A C E T Q R)
  change _ ≫ whiskerRight
      ((derivedBimoduleComposeFunctor A B C T hT).map i.hom ≫ _) RO =
    whiskerLeft RI ((derivedBimoduleComposeFunctor A D C T hT).map i.hom ≫ _) ≫ _
  rw [whiskerRight_comp, whiskerLeft_comp]
  simp only [Category.assoc]
  change _ ≫ (rightRestrictionDerivedComposeTarget A B D C T F hT).map i.hom ≫ _ = _
  rw [← reassoc_of% hn, hm]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
