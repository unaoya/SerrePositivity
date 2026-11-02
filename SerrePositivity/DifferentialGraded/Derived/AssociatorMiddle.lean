module

public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeft
public import SerrePositivity.DifferentialGraded.Derived.Functor
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.IteratedModels
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Coherence

/-!
# Derived.AssociatorMiddle

## 概要
17 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## AssociatorMiddleRestrictionKFlat（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionKFlat.lean） -/

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

@[expose] public section AssociatorMiddleRestrictionKFlat
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorMiddleRestrictionKFlat

/-! ## AssociatorMiddleRestrictionPresentation（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionPresentation.lean） -/

/-! # 実際の全導来中間比較を指定K-flatモデルで計算する

## 概要
実際の全導来中間比較を指定K-flatモデルで計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionPresentation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D E hE
local notation "KS" => rightKFlatDerivedCompose A B D E S
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RQ" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A C D E F) Q.obj

/-- 後因子の制限表示と指定増大の既存計算同型による、全導来sourceの表示。 -/
def middleRestrictionKFlatSourceIso :
    (middleRestrictionDerivedSource A B C D E F hE).obj QT ≅ L ⋙ KS :=
  Functor.isoWhiskerLeft L
    ((HD).mapIso ((middleRightRestrictionDerivedIso A C D F E).app Q.obj).symm ≪≫
      derivedBimoduleComposeResolutionComputation A B D E hE RQ S q hq)

/-- 元の前因子上で、source表示は前因子の制限表示と解像度計算を交換する。 -/
lemma middleRestrictionKFlatSourceIso_base_calculation (P : BimoduleCategory A B C) :
    (middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P ≫
      (middleRestrictionKFlatSourceIso A B C D E F hE Q S q hq).hom.app
        ((bimoduleToDerived A B C).obj P) =
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj S q hq).hom ≫
      (derivedComposeWithComputation A B D E S.obj S.property
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)).inv ≫
      (KS).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) := by
  let X := (L).obj ((bimoduleToDerived A B C).obj P)
  have hc := congrArg (fun k => ((HD).map k).app X)
    ((middleRightRestrictionDerivedIso A C D F E).hom_inv_id_app Q.obj)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id,
    NatTrans.comp_app, NatTrans.id_app] at hc
  have hn := (derivedBimoduleComposeResolutionComputation A B D E hE RQ S q hq).hom.naturality
    ((middleLeftRestrictionDerivedIso A B C D F).hom.app P)
  rw [middleDerivedSourceFamilyIdentification_hom_app_calc]
  simp only [middleRestrictionKFlatSourceIso, Functor.isoWhiskerLeft_hom,
    whiskerLeft_app, Iso.trans_hom, NatTrans.comp_app, CategoryTheory.Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  change _ = (_ ≫ 𝟙 _) ≫ 𝟙 _ ≫ _
  simp only [Category.comp_id, Category.id_comp]
  exact hn

private lemma model_square {V : Type*} [Category* V] {x y z w t v : V}
    (e : x ≅ y) (r : x ≅ z) (a : y ⟶ w) (b : w ⟶ v)
    (c : y ⟶ t) (d : t ⟶ v) (σ : z ⟶ t) (f : z ⟶ v)
    (hc : e.hom ≫ c = r.hom ≫ σ) (hd : σ ≫ d = f)
    (ha : r.inv ≫ e.hom ≫ a ≫ b = f) : a ≫ b = c ≫ d := by
  apply (Iso.cancel_iso_hom_left e _ _).1
  calc
    _ = r.hom ≫ f := by
      simpa only [Category.assoc, r.hom_inv_id_assoc] using congrArg (fun k => r.hom ≫ k) ha
    _ = _ := by rw [← hd, ← Category.assoc, ← hc, Category.assoc]

/-- 実際の全導来中間比較は、指定K-flatモデルの比較をsource表示とtarget表示で挟んだもの。 -/
lemma derivedMiddleRestrictionNatTrans_kFlat_model_calculation :
    (derivedMiddleRestrictionNatTrans A B C D E F hE).app QT ≫
      (derivedBimoduleComposeKFlatIso A B C E hE Q).hom =
    (middleRestrictionKFlatSourceIso A B C D E F hE Q S q hq).hom ≫
      rightKFlatMiddleComparison A B C D E F Q S q := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app]
  exact model_square
    ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).app P)
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj S q hq) _ _ _ _ _ _
    (middleRestrictionKFlatSourceIso_base_calculation A B C D E F hE Q S q hq P)
    (by
      have h := rightKFlatMiddleComparison_base_square A B C D E F Q S q P
      change (𝟙 _ ≫ _) ≫ _ = _
      rw [Category.id_comp]
      exact h)
    (derivedMiddleRestrictionNatTrans_resolution_calculation A B C D E F hE P Q S q hq)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionPresentation

/-! ## AssociatorMiddleRestrictionFactors（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionFactors.lean） -/

/-! # 中間制限後の指定モデルと結合子比較に使う因子同型

## 概要
中間制限後の指定モデルと結合子比較に使う因子同型。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionFactors
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "HD" => derivedBimoduleComposeFunctor A B D E hE
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj

/-- 既存の導来制限を、指定した制限後K-flatモデルの局所化像へ同定する。 -/
def middleRestrictionKFlatFactorIso :
    (derivedBimoduleRestriction A D E C E F (DGFunctor.id E)).obj QT ≅
      (bimoduleToDerived A D E).obj S.obj :=
  ((middleRightRestrictionDerivedIso A C D F E).app Q.obj).symm ≪≫
    (bimoduleDerivedIso A D E q hq).symm

/-- 因子同型の逆は、指定増大の局所化と既存制限表示を続けた射。 -/
lemma middleRestrictionKFlatFactorIso_inv :
    (middleRestrictionKFlatFactorIso A C D E F Q S q hq).inv =
      (bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj := rfl

/-- 中間比較のsource表示は、同じ因子同型と固定合成表示によるもの。 -/
lemma middleRestrictionKFlatSourceIso_hom :
    (middleRestrictionKFlatSourceIso A B C D E F hE Q S q hq).hom =
      whiskerLeft L
        ((HD).map (middleRestrictionKFlatFactorIso A C D E F Q S q hq).hom ≫
          (derivedBimoduleComposeKFlatIso A B D E hE S).hom) := by
  simp only [middleRestrictionKFlatSourceIso, middleRestrictionKFlatFactorIso,
    derivedBimoduleComposeResolutionComputation, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, CategoryTheory.Functor.mapIso_hom,
    CategoryTheory.Functor.map_comp, whiskerLeft_comp, Category.assoc]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionFactors

/-! ## AssociatorMiddleRestrictionAugmentation（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionAugmentation.lean） -/

/-! # 制限後の増大の合成と固定K-flat外側右比較の可換square

## 概要
制限後の増大の合成と固定K-flat外側右比較の可換square。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionAugmentation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (Q : BimoduleCategory A C E) (S : BimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "KR" => rightKFlatDerivedCompose A D E T R
local notation "QR" => BimoduleCategory.of A C T
  (compose A C E T (BimoduleCategory.underlying A C E Q)
    (BimoduleCategory.underlying A E T R.obj))

/-- 任意の増大の合成は、入力・出力の既存制限表示と固定K-flat右比較を保つ。 -/
lemma rightKFlatMiddleComposeAugmentation_square :
    (KR).map ((bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q) ≫
      (derivedComposeWithRightRestrictionIso A C D E T F R).hom.app
        ((bimoduleToDerived A C E).obj Q) =
    (bimoduleToDerived A D T).map
        (middleRestrictionComposeAugmentation A C D E T F Q S R.obj q) ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app QR := by
  have hc := congrArg (fun k => (KR).map k)
    ((middleRightRestrictionDerivedIso A C D F E).hom_inv_id_app Q)
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [derivedComposeWithRightRestrictionIso_base_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  have hm := rightKFlatDerivedCompose_map_base A D E T R q
  rw [hm]
  simp only [middleRestrictionComposeAugmentation, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionAugmentation

/-! ## AssociatorMiddleRestrictionInner（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionInner.lean） -/

/-! # 中間制限後の合成増大と実際の全導来内側比較のモデルsquare

## 概要
中間制限後の合成増大と実際の全導来内側比較のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionInner
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : BimoduleCategory A C E) (S : BimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q)

local notation "HR" => Functor.obj (derivedBimoduleComposeFunctor A D E T hT)
  (Functor.obj (bimoduleToDerived A E T) R.obj)
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "QR" => BimoduleCategory.of A C T
  (compose A C E T (BimoduleCategory.underlying A C E Q)
    (BimoduleCategory.underlying A E T R.obj))

/-- 全導来内側右比較を増大で前置し、固定Rの計算同型で挟むと合成増大の局所化になる。 -/
lemma middleRestrictionInnerAugmentation_model_square :
    (HR).map ((bimoduleToDerived A D E).map q ≫
        (middleRightRestrictionDerivedIso A C D F E).hom.app Q) ≫
      ((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app
        ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q) ≫
      (RI).map (derivedBimoduleComposeKFlatValueIso A C E T hT R Q).hom =
    (derivedBimoduleComposeKFlatValueIso A D E T hT R S).hom ≫
      (bimoduleToDerived A D T).map
        (middleRestrictionComposeAugmentation A C D E T F Q S R.obj q) ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app QR := by
  let u := (bimoduleToDerived A D E).map q ≫
    (middleRightRestrictionDerivedIso A C D F E).hom.app Q
  have hn := (derivedBimoduleComposeKFlatIso A D E T hT R).hom.naturality u
  have hm := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_model_calculation A C D E T F hT R)
    ((bimoduleToDerived A C E).obj Q)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hm
  have ha := rightKFlatMiddleComposeAugmentation_square A C D E T F Q S R q
  change (HR).map u ≫ _ ≫ _ = _
  erw [hm]
  rw [← Category.assoc ((HR).map u)]
  erw [hn]
  rw [Category.assoc, ha]
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionInner

/-! ## AssociatorMiddleRestrictionInnerModel（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionInnerModel.lean） -/

/-! # 第一中間制限の全導来内側比較と指定二因子モデルの表示

## 概要
第一中間制限の全導来内側比較と指定二因子モデルの表示。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionInnerModel
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E) (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "HR" => Functor.obj (derivedBimoduleComposeFunctor A D E T hT) RT
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "qR" => middleRestrictionComposeAugmentation A C D E T F Q.obj S.obj R.obj q

/-- 内側の全導来右比較は、指定二因子の表示を通すと合成増大の局所化になる。 -/
lemma derivedMiddleRestriction_inner_model_square :
    ((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app RT).app QT ≫
      (RI).map (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A D E T hT S R eS (Iso.refl _)).hom ≫
      (bimoduleToDerived A D T).map qR ≫
      (middleRightRestrictionDerivedIso A C D F T).hom.app (QR).obj := by
  have hs := middleRestrictionInnerAugmentation_model_square A C D E T F hT Q.obj S.obj R q
  rw [← middleRestrictionKFlatFactorIso_inv A C D E F Q S q hq] at hs
  have hc := congrArg (fun k => (HR).map k) (eS).hom_inv_id
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  have h := congrArg (fun k => (HR).map (eS).hom ≫ k) hs
  rw [reassoc_of% hc] at h
  convert h using 1 <;>
    simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom,
    Iso.app_hom, CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionInnerModel

/-! ## AssociatorMiddleRestrictionNested（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionNested.lean） -/

/-! # 第一中間制限と全導来結合子の入れ子側のモデルsquare

## 概要
第一中間制限と全導来結合子の入れ子側のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionNested
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (S : RightKFlatBimoduleCategory A D E) (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RI" => derivedBimoduleRestriction A D T C T F (DGFunctor.id T)
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "SR" => rightKFlatCompose A D E T S R
local notation "qR" => middleRestrictionComposeAugmentation A C D E T F Q.obj S.obj R.obj q
local notation "hqR" => middleRestrictionComposeAugmentation_quasiIso A C D E T F
  Q.obj S.obj R.obj q R.property hq
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq
local notation "jC" => derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
  (Iso.refl _) (Iso.refl _)
local notation "jD" => derivedBimoduleComposeInnerComparisonIso A D E T hT S R eS (Iso.refl _)
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT
local notation "k" => NatTrans.app
  (NatTrans.app (Iso.hom (derivedBimoduleComposeRightRestrictionIso A C D E T F hT)) RT) QT

private lemma paste_nested {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d : V} {x y z t : W} (f : a ⟶ b) (u : b ⟶ c) (j : a ⟶ d) (s : c ≅ d)
    (βb : H.obj b ⟶ x) (βc : H.obj c ⟶ y) (v : x ⟶ y)
    (out : y ⟶ z) (r : H.obj d ⟶ t) (β : t ⟶ z)
    (hi : f ≫ u = j ≫ s.inv) (hn : H.map u ≫ βc = βb ≫ v)
    (hm : βc ≫ out = H.map s.hom ≫ r ≫ β) :
    H.map f ≫ βb ≫ v ≫ out = H.map j ≫ r ≫ β := by
  calc
    _ = H.map (f ≫ u) ≫ βc ≫ out := by rw [H.map_comp, Category.assoc, reassoc_of% hn]
    _ = H.map j ≫ H.map s.inv ≫ βc ≫ out := by
      rw [hi, H.map_comp, Category.assoc]
    _ = _ := by
      rw [hm, ← Category.assoc (H.map s.inv) (H.map s.hom),
        ← H.map_comp, s.inv_hom_id, H.map_id, Category.id_comp]

/-- 内側の指定モデルsquareと全導来中間比較の自然性を貼り合わせた式。 -/
lemma derivedMiddleRestriction_nested_prefix_square :
    whiskerLeft L ((HD).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U ≫
      (derivedBimoduleComposeFunctor A B C T hT).map (jC).hom ≫
      (derivedBimoduleComposeKFlatIso A B C T hT QR).hom =
    whiskerLeft L ((HD).map (jD).hom) ≫
      whiskerLeft L (derivedBimoduleComposeKFlatIso A B D T hT SR).hom ≫
      rightKFlatMiddleComparison A B C D T F QR SR qR := by
  let H := HD ⋙ (whiskeringLeft _ _ _).obj L
  let s := middleRestrictionKFlatFactorIso A C D T F QR SR qR hqR
  have hi := derivedMiddleRestriction_inner_model_square A C D E T F hT Q S R q hq
  rw [← middleRestrictionKFlatFactorIso_inv A C D T F QR SR qR hqR] at hi
  have hn := (derivedMiddleRestrictionNatTrans A B C D T F hT).naturality (jC).hom
  have hm := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B C D T F hT
    QR SR qR hqR
  rw [middleRestrictionKFlatSourceIso_hom, whiskerLeft_comp] at hm
  simp only [Category.assoc] at hm
  have h := paste_nested H k ((RI).map (jC).hom) (jD).hom s
    ((derivedMiddleRestrictionNatTrans A B C D T F hT).app U)
    ((derivedMiddleRestrictionNatTrans A B C D T F hT).app
      ((bimoduleToDerived A C T).obj (QR).obj))
    ((derivedBimoduleComposeFunctor A B C T hT).map (jC).hom)
    (derivedBimoduleComposeKFlatIso A B C T hT QR).hom
    (whiskerLeft L (derivedBimoduleComposeKFlatIso A B D T hT SR).hom)
    (rightKFlatMiddleComparison A B C D T F QR SR qR) hi hn hm
  convert h using 1 <;> rfl

/-- 入れ子合成の既存表示を通すと、実際の全導来中間比較が固定モデルの比較へ戻る。 -/
lemma derivedMiddleRestriction_nested_model_square :
    whiskerLeft L ((HD).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U ≫
      (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    whiskerLeft L (derivedBimoduleComposeNestedComparisonIso A B D E T hT S R
        eS (Iso.refl _)).hom ≫
      rightKFlatMiddleComparison A B C D T F QR SR qR := by
  have h := derivedMiddleRestriction_nested_prefix_square A B C D E T F hT Q S R q hq
  simpa only [derivedBimoduleComposeNestedComparisonIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, whiskerLeft_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionNested

/-! ## AssociatorMiddleRestrictionPair（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionPair.lean） -/

/-! # 第一中間制限と全導来結合子の二段階合成側のモデルsquare

## 概要
第一中間制限と全導来結合子の二段階合成側のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionPair
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (S : RightKFlatBimoduleCategory A D E)
  (R : RightKFlatBimoduleCategory A E T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "eS" => middleRestrictionKFlatFactorIso A C D E F Q S q hq

private lemma paste_pair {V W X : Type*} [Category* V] [Category* W] [Category* X]
    {F G J K : V ⥤ W} (a : F ⟶ G) (b : G ⟶ K) (c : F ⟶ J) (d : J ⟶ K)
    (H H' : W ⥤ X) (r : H ⟶ H') (hm : a ≫ b = c ≫ d) :
    whiskerRight a H ≫ whiskerRight b H ≫ whiskerLeft K r =
      whiskerRight c H ≫ whiskerLeft J r ≫ whiskerRight d H' := by
  apply NatTrans.ext
  funext P
  have h := congrArg (fun k => H.map k ≫ r.app (K.obj P)) (NatTrans.congr_app hm P)
  simp only [NatTrans.comp_app, CategoryTheory.Functor.map_comp] at h
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  calc
    _ = H.map (c.app P) ≫ H.map (d.app P) ≫ r.app (K.obj P) := by
      simpa only [Category.assoc] using h
    _ = _ := by rw [r.naturality]

/-- 二段階合成の既存表示を通すと、実際の中間比較が指定K-flatモデルの比較に戻る。 -/
lemma derivedMiddleRestriction_pair_model_square :
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    whiskerLeft L (derivedBimoduleComposePairComparisonIso A B D E T hE hT S R
        eS (Iso.refl _)).hom ≫
      whiskerRight (rightKFlatMiddleComparison A B C D E F Q S q)
        (rightKFlatDerivedCompose A B E T R) := by
  have hm := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B C D E F hE Q S q hq
  rw [middleRestrictionKFlatSourceIso_hom] at hm
  have h := paste_pair _ _ _ _ _ _ (derivedBimoduleComposeKFlatIso A B E T hT R).hom hm
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      whiskerLeft_id', whiskerRight_id', whiskerLeft_comp, whiskerRight_comp,
      Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionPair

/-! ## AssociatorMiddleRestrictionModel（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionModel.lean） -/

/-! # 第一中間制限と実際の全導来結合子のモデル上のcoherence

## 概要
第一中間制限と実際の全導来結合子のモデル上のcoherence。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionModel
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RQD" => Functor.obj
  (derivedBimoduleRestriction A D E C E F (DGFunctor.id E)) QT
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT
local notation "k" => NatTrans.app
  (NatTrans.app (Iso.hom (derivedBimoduleComposeRightRestrictionIso A C D E T F hT)) RT) QT

private lemma post_paste {V : Type*} [Category* V] {a b c d e f : V}
    (α : b ⟶ c) (t : c ⟶ d) (p : b ⟶ e) (α' : e ⟶ d)
    (γ : a ⟶ b) (s : a ⟶ f) (γ' : f ⟶ e)
    (ht : α ≫ t = p ≫ α') (hp : γ ≫ p = s ≫ γ') :
    (γ ≫ α) ≫ t = s ≫ (γ' ≫ α') := by
  rw [Category.assoc, ht, ← Category.assoc γ p, hp, Category.assoc]

private lemma paste_associator_middle {V : Type*} [Category* V]
    {a b c a' b' c' : V} (α : a ⟶ b) (β : b ⟶ c) (r : a ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (r' : a' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hr : r ≫ t.hom = s.hom ≫ r') (hm : α' ≫ β' = r') : α ≫ β = r := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = s.hom ≫ α' ≫ β' := by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ r' := by rw [hm]
    _ = _ := hr.symm

/-- 指定した制限後K-flatモデルで、実際の全導来結合子と第一中間比較が可換。 -/
lemma derivedBimoduleAssociator_middleRestriction_model
    (S : RightKFlatBimoduleCategory A D E)
    (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT RQD RT).hom ≫
      whiskerLeft L ((derivedBimoduleComposeFunctor A B D T hT).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom := by
  let eS := middleRestrictionKFlatFactorIso A C D E F Q S q hq
  let pD := derivedBimoduleComposePairComparisonIso A B D E T hE hT S R eS (Iso.refl _)
  let nD := derivedBimoduleComposeNestedComparisonIso A B D E T hT S R eS (Iso.refl _)
  let nC := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := congrArg (fun f => whiskerLeft L f)
    (derivedBimoduleAssociator_comparison_fac A B D E T hE hT S R eS (Iso.refl _))
  simp only [whiskerLeft_comp] at ha
  have hb := derivedMiddleRestriction_nested_model_square A B C D E T F hT Q S R q hq
  have ht := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have hp := derivedMiddleRestriction_pair_model_square A B C D E T F hE hT Q S R q hq
  have hr := post_paste _ _ _ _ _ _ _ ht hp
  have hm := rightKFlatDerivedAssociator_middleRestriction A B C D E T F Q S R q
  exact paste_associator_middle _ _ _ (Functor.isoWhiskerLeft L pD)
    (Functor.isoWhiskerLeft L nD) nC _ _ _ ha
    (by simpa only [Functor.isoWhiskerLeft_hom, nD, nC, eS, Category.assoc] using hb) hr hm

/-- 後二因子がK-flatなら、制限後には既存の標準分解を取り、追加条件なしで可換になる。 -/
lemma derivedBimoduleAssociator_middleRestriction_rightKFlat :
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT RQD RT).hom ≫
      whiskerLeft L ((derivedBimoduleComposeFunctor A B D T hT).map k) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app U =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app QT)
        ((derivedBimoduleComposeFunctor A B E T hT).obj RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom := by
  let M := (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj
  exact derivedBimoduleAssociator_middleRestriction_model A B C D E T F hE hT Q R
    (rightKFlatResolutionObj A D E hE M) (bimoduleCanonicalSemifreeResolution A D E M).π
    (bimoduleCanonicalSemifreeResolution A D E M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionModel

/-! ## AssociatorMiddleRestrictionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionFamilies.lean） -/

/-! # 第一中間制限と全導来結合子の両経路の三変数自然性

## 概要
第一中間制限と全導来結合子の両経路の三変数自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorMiddleRestrictionFamilies
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)

local notation "X" => DerivedBimoduleCategory A B C
local notation "XD" => DerivedBimoduleCategory A B D
local notation "Y" => DerivedBimoduleCategory A C E
local notation "YD" => DerivedBimoduleCategory A D E
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A B T
local notation "BE" => DerivedBimoduleCategory A B E
local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "RQ" => derivedBimoduleRestriction A D E C E F (DGFunctor.id E)
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "HR" => derivedBimoduleComposeFunctor A C E T hT
local notation "HBR" => derivedBimoduleComposeFunctor A B E T hT
local notation "preQ" => Functor.obj (whiskeringLeft Y YD (XD ⥤ W)) RQ
local notation "preP" => Functor.obj (whiskeringRight Y (XD ⥤ W) (X ⥤ W))
  (Functor.obj (whiskeringLeft X XD W) L)

/-- 最初の中間圏を制限した後の二段階合成の、全三変数のsource関手族。 -/
def middleRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorSource A B D E T hE hT ⋙ preQ ⋙ preP

/-- 制限後の結合子、内側右比較、中間比較を続ける経路。 -/
def middleRestrictionAssociatorLeftPath :
    middleRestrictionAssociatorSource A B C D E T F hE hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerRight (derivedBimoduleAssociatorIso A B D E T hE hT).hom (preQ ⋙ preP) ≫
    whiskerRight (derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom
      ((whiskeringRight Y (DerivedBimoduleCategory A D T) (XD ⥤ W)).obj HD ⋙ preP) ≫
    whiskerLeft HR ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).map
      (derivedMiddleRestrictionNatTrans A B C D T F hT))

/-- 中間比較を後因子との合成へ送った後、元の結合子を続ける経路。 -/
def middleRestrictionAssociatorRightPath :
    middleRestrictionAssociatorSource A B C D E T F hE hT ⟶
      derivedBimoduleAssociatorTarget A B C E T hT :=
  whiskerLeft (HBR ⋙ whiskeringRight X BE W)
      ((whiskeringLeft Y (X ⥤ BE) (X ⥤ W)).map
        (derivedMiddleRestrictionNatTrans A B C D E F hE)) ≫
    (derivedBimoduleAssociatorIso A B C E T hE hT).hom

lemma middleRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((middleRestrictionAssociatorLeftPath A B C D E T F hE hT).app R).app Q =
    whiskerLeft L (derivedBimoduleAssociator A B D E T hE hT ((RQ).obj Q) R).hom ≫
      whiskerLeft L ((HD).map
        (((derivedBimoduleComposeRightRestrictionIso A C D E T F hT).hom.app R).app Q)) ≫
      (derivedMiddleRestrictionNatTrans A B C D T F hT).app (((HR).obj R).obj Q) := rfl

lemma middleRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((middleRestrictionAssociatorRightPath A B C D E T F hE hT).app R).app Q =
    whiskerRight ((derivedMiddleRestrictionNatTrans A B C D E F hE).app Q) ((HBR).obj R) ≫
      (derivedBimoduleAssociator A B C E T hE hT Q R).hom := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorMiddleRestrictionFamilies

/-! ## AssociatorMiddleRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorMiddleRestrictionCoherence.lean） -/

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

@[expose] public section AssociatorMiddleRestrictionCoherence
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorMiddleRestrictionCoherence

/-! ## AssociatorSecondMiddleRestrictionKFlat（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionKFlat.lean） -/

/-! # 第二中間圏の指定K-flatモデルと導来結合子のcoherence

## 概要
第二中間圏の指定K-flatモデルと導来結合子のcoherence。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionKFlat
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)
  (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)

local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "QS" => rightKFlatCompose A C D T LQ S
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "g" => middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q

/-- 第二中間比較と外側左比較は、固定K-flat導来結合子の二経路を同一視する。 -/
lemma rightKFlatDerivedAssociator_secondMiddleRestriction :
    whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
        (rightKFlatDerivedCompose A B D T S) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatMiddleComparison A B E D T F R S q) ≫
      (rightKFlatDerivedAssociator A B C E T Q R).hom =
    (rightKFlatDerivedAssociator A B C D T LQ S).hom ≫
      rightKFlatDerivedMap A B C T (Q := QS) (Q' := QR) g := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  have hβ := derivedComposeWithLeftRestrictionIso_base_app A B C E D F Q P
  have hm := rightKFlatMiddleComparison_base_app A B E D T F R S q
    ((composeWith A B C E Q.obj).obj P)
  have hα := rightKFlatDerivedAssociator_base_app A B C E T Q R P
  have hα' := rightKFlatDerivedAssociator_base_app A B C D T LQ S P
  have hg := rightKFlatDerivedMap_base_app A B C T (Q := QS) (Q' := QR) g P
  rw [hβ, hα, hα', hg]
  erw [hm]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hc := congrArg (fun k => (rightKFlatDerivedCompose A B D T S).map k)
    ((middleLeftRestrictionDerivedIso A B E D F).hom_inv_id_app
      ((composeWith A B C E Q.obj).obj P))
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] at hc
  rw [reassoc_of% hc]
  have hmap := rightKFlatDerivedCompose_map_base A B D T S
    (composeLeftRestrictionIso A B C E D F P Q.obj).hom
  rw [hmap]
  have hs := congrArg ((bimoduleToDerived A B T).map)
    (associatorIso_secondMiddleRestriction_resolved A B C D E T F P Q.obj R.obj S.obj q)
  simp only [CategoryTheory.Functor.map_comp] at hs
  convert hs using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionKFlat

/-! ## AssociatorSecondMiddleRestrictionInner（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionInner.lean） -/

/-! # 第二中間制限の内側全導来比較と指定K-flatモデルの表示

## 概要
第二中間制限の内側全導来比較と指定K-flatモデルの表示。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionInner
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hT : localHomKFlat A T) (Q : RightKFlatBimoduleCategory A C E)
  (R : RightKFlatBimoduleCategory A E T) (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
  (hq : BimoduleCategory.quasiIso A D T q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "HD" => derivedBimoduleComposeFunctor A C D T hT
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "LQD" => Functor.obj
  (derivedBimoduleRestriction A C D C E (DGFunctor.id C) F) QT
local notation "eS" => middleRestrictionKFlatFactorIso A E D T F R S q hq
local notation "KS" => rightKFlatDerivedCompose A C D T S
local notation "g" => middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q

/-- source表示を制限後Qの表示へ進めると、同じ二因子モデルの前半になる。 -/
lemma derivedSecondMiddleRestriction_inner_prefix_square :
    (middleRestrictionKFlatSourceIso A C E D T F hT R S q hq).hom.app QT ≫
      (KS).map ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) =
    ((HD).obj RRD).map ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
      ((HD).map (eS).hom).app ((bimoduleToDerived A C D).obj (LQ).obj) ≫
      (derivedBimoduleComposeKFlatIso A C D T hT S).hom.app
        ((bimoduleToDerived A C D).obj (LQ).obj) := by
  have h := ((HD).map (eS).hom ≫
    (derivedBimoduleComposeKFlatIso A C D T hT S).hom).naturality
      ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj)
  simp only [NatTrans.comp_app, Category.assoc] at h
  rw [middleRestrictionKFlatSourceIso_hom]
  simp only [whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  convert h.symm using 1 <;> rfl

/-- 内側の実際の全導来中間比較は、指定モデルで既存の通常解像度比較射へ計算される。 -/
lemma derivedSecondMiddleRestriction_inner_model_square :
    ((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT ≫
      (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A C D T hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom ≫
      (bimoduleToDerived A C T).map g := by
  have hm := NatTrans.congr_app
    (derivedMiddleRestrictionNatTrans_kFlat_model_calculation A C E D T F hT R S q hq) QT
  simp only [NatTrans.comp_app] at hm
  rw [rightKFlatMiddleComparison_base_app] at hm
  have hp := derivedSecondMiddleRestriction_inner_prefix_square A C D E T F hT Q R S q hq
  rw [← Category.assoc
    ((middleRestrictionKFlatSourceIso A C E D T F hT R S q hq).hom.app QT), hp] at hm
  simp only [Category.assoc] at hm
  convert hm using 1 <;>
    simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionInner

/-! ## AssociatorSecondMiddleRestrictionNested（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionNested.lean） -/

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

@[expose] public section AssociatorSecondMiddleRestrictionNested
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorSecondMiddleRestrictionNested

/-! ## AssociatorSecondMiddleRestrictionPair（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionPair.lean） -/

/-! # 第二中間制限と全導来結合子の二段階合成側のモデルsquare

## 概要
第二中間制限と全導来結合子の二段階合成側のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionPair
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hD : localHomKFlat A D) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)
  (S : RightKFlatBimoduleCategory A D T)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
  (hq : BimoduleCategory.quasiIso A D T q)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "L" => derivedBimoduleRestriction A B D B E (DGFunctor.id B) F
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT
local notation "eS" => middleRestrictionKFlatFactorIso A E D T F R S q hq
local notation "aQIso" => Iso.app
  (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD) Q
local notation "sIso" => Iso.trans (Functor.mapIso HD eS)
  (derivedBimoduleComposeKFlatIso A B D T hT S)

/-- 二段階合成の表示は、前の因子の表示を先に行う順序へ自然性で正規化できる。 -/
lemma derivedSecondMiddleRestriction_pair_comparison_hom :
    (derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom =
    whiskerRight (aQIso).hom ((HD).obj RRD) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C D LQ) (sIso).hom := by
  apply NatTrans.ext
  funext P
  have hn := ((HD).map (eS).hom).naturality
    ((derivedBimoduleComposeKFlatIso A B C D hD LQ).hom.app P)
  simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]

private lemma paste_horizontal {V W X : Type*} [Category* V] [Category* W] [Category* X]
    (U : W ⥤ V) (H K : V ⥤ X) (J M : W ⥤ X)
    (b : U ⋙ H ⟶ J) (b' : U ⋙ K ⟶ M) (k : H ⟶ K) (l : J ⟶ M)
    (hb : b ≫ l = whiskerLeft U k ≫ b')
    {x x' : V} {y y' : W} (a : x ⟶ U.obj y) (v : y ⟶ y')
    (w : x ⟶ x') (a' : x' ⟶ U.obj y') (ha : a ≫ U.map v = w ≫ a') :
    H.map a ≫ b.app y ≫ J.map v ≫ l.app y' =
      H.map w ≫ k.app x' ≫ K.map a' ≫ b'.app y' := by
  have hn := b.naturality v
  have hm := congrArg H.map ha
  have hc := NatTrans.congr_app hb y'
  simp only [Functor.comp_map] at hn
  simp only [CategoryTheory.Functor.map_comp] at hm
  simp only [NatTrans.comp_app, whiskerLeft_app] at hc
  calc
    _ = H.map a ≫ H.map (U.map v) ≫ b.app y' ≫ l.app y' := by rw [← reassoc_of% hn]
    _ = H.map w ≫ H.map a' ≫ b.app y' ≫ l.app y' := by
      rw [← Category.assoc (H.map a), hm, Category.assoc]
    _ = H.map w ≫ H.map a' ≫ k.app (U.obj y') ≫ b'.app y' := by rw [hc]
    _ = _ := by rw [← reassoc_of% (k.naturality a')]

/-- 二段階の実際の外側左比較・中間比較は、指定K-flatモデルの二段階比較に戻る。 -/
lemma derivedSecondMiddleRestriction_pair_model_square (hE : localHomKFlat A E) :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S
        ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm eS).hom ≫
      whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
        (rightKFlatDerivedCompose A B D T S) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (rightKFlatMiddleComparison A B E D T F R S q) := by
  have ha := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app] at ha
  have hb := derivedMiddleRestrictionNatTrans_kFlat_model_calculation A B E D T F hT R S q hq
  rw [middleRestrictionKFlatSourceIso_hom] at hb
  rw [derivedSecondMiddleRestriction_pair_comparison_hom]
  apply NatTrans.ext
  funext P
  have hc := NatTrans.congr_app ha P
  simp only [NatTrans.comp_app, whiskerRight_app] at hc
  have h := paste_horizontal L _ _ _ _ _ _ (sIso).hom _ hb _ _ _ _ hc
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      whiskerLeft_id', whiskerRight_id', NatTrans.comp_app, whiskerLeft_app,
      whiskerRight_app, Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionPair

/-! ## AssociatorSecondMiddleRestrictionModel（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionModel.lean） -/

/-! # 第二中間制限と実際の全導来結合子のモデル上のcoherence

## 概要
第二中間制限と実際の全導来結合子のモデル上のcoherence。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorSecondMiddleRestrictionModel
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "LQD" => Functor.obj
  (derivedBimoduleRestriction A C D C E (DGFunctor.id C) F) QT
local notation "RRD" => Functor.obj
  (derivedBimoduleRestriction A D T E T F (DGFunctor.id T)) RT
local notation "HD" => derivedBimoduleComposeFunctor A B D T hT

private lemma post_paste_second_middle {V : Type*} [Category* V] {a b c d e f : V}
    (α : a ⟶ b) (γ : b ⟶ c) (n : b ⟶ d) (t : c ⟶ e)
    (p : a ⟶ f) (α' : f ⟶ d) (γ' : d ⟶ e)
    (ha : α ≫ n = p ≫ α') (hb : γ ≫ t = n ≫ γ') :
    (α ≫ γ) ≫ t = p ≫ (α' ≫ γ') := by
  rw [Category.assoc, hb, ← Category.assoc α n, ha, Category.assoc]

private lemma paste_associator_second_middle {V : Type*} [Category* V]
    {a b c a' b' c' : V} (α : a ⟶ b) (β : b ⟶ c) (r : a ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (r' : a' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hr : r ≫ t.hom = s.hom ≫ r') (hm : α' ≫ β' = r') : α ≫ β = r := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = s.hom ≫ α' ≫ β' := by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ r' := by rw [hm]
    _ = _ := hr.symm

/-- 指定した制限後K-flatモデルで、実際の全導来結合子と第二中間比較が可換。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction_model
    (S : RightKFlatBimoduleCategory A D T)
    (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj)
    (hq : BimoduleCategory.quasiIso A D T q) :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom =
    (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT) := by
  let eS := middleRestrictionKFlatFactorIso A E D T F R S q hq
  let eQ := ((middleLeftRestrictionDerivedIso A C E D F).app Q.obj).symm
  let pD := derivedBimoduleComposePairComparisonIso A B C D T hD hT LQ S eQ eS
  let nD := derivedBimoduleComposeNestedComparisonIso A B C D T hT LQ S eQ eS
  let pC := derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nC := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := derivedSecondMiddleRestriction_pair_model_square A B C D E T F hD hT Q R S q hq hE
  have hb := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have ht := derivedBimoduleAssociator_comparison_fac A B C D T hD hT LQ S eQ eS
  have hn := derivedSecondMiddleRestriction_nested_model_square A B C D E T F hT Q R S q hq
  have hr := post_paste_second_middle _ _ _ _ _ _ _ ht hn
  have hm := rightKFlatDerivedAssociator_secondMiddleRestriction A B C D E T F Q R S q
  let a := whiskerRight
      ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
      ((HD).obj RRD) ≫
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
      ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT)
  let a' := whiskerRight (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom
      (rightKFlatDerivedCompose A B D T S) ≫
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
      (rightKFlatMiddleComparison A B E D T F R S q)
  let r := (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
    (derivedBimoduleComposeFunctor A B C T hT).map
      (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT)
  let r' := (rightKFlatDerivedAssociator A B C D T LQ S).hom ≫
    rightKFlatDerivedMap A B C T (Q := rightKFlatCompose A C D T LQ S)
      (Q' := rightKFlatCompose A C E T Q R)
      (middleRestrictionResolvedMap A C E D T F Q.obj R.obj S.obj q)
  have h := paste_associator_second_middle a (derivedBimoduleAssociator A B C E T hE hT QT RT).hom r
    pD pC nC a' (rightKFlatDerivedAssociator A B C E T Q R).hom r'
    (by simpa only [a, a', pC, pD, eQ, eS, Category.assoc] using ha) hb
    (by simpa only [r, r', eQ, eS, nD, nC, pD, leftRestrictionDerivedComposeTarget,
      Functor.comp_obj, Category.assoc] using hr)
    (by simpa only [a', r', Category.assoc] using hm)
  simpa only [a, r, Category.assoc] using h

/-- 制限後には既存の標準K-flat分解を取り、後二因子のモデル以外の条件を追加せず可換にする。 -/
lemma derivedBimoduleAssociator_secondMiddleRestriction_rightKFlat :
    whiskerRight
        ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app QT)
        ((HD).obj RRD) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedMiddleRestrictionNatTrans A B E D T F hT).app RT) ≫
      (derivedBimoduleAssociator A B C E T hE hT QT RT).hom =
    (derivedBimoduleAssociator A B C D T hD hT LQD RRD).hom ≫
      (derivedBimoduleComposeFunctor A B C T hT).map
        (((derivedMiddleRestrictionNatTrans A C E D T F hT).app RT).app QT) := by
  let M := (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R.obj
  exact derivedBimoduleAssociator_secondMiddleRestriction_model A B C D E T F hE hD hT Q R
    (rightKFlatResolutionObj A D T hT M) (bimoduleCanonicalSemifreeResolution A D T M).π
    (bimoduleCanonicalSemifreeResolution A D T M).quasiIso

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorSecondMiddleRestrictionModel

/-! ## AssociatorSecondMiddleRestrictionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorSecondMiddleRestrictionFamilies.lean） -/

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

@[expose] public section AssociatorSecondMiddleRestrictionFamilies
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorSecondMiddleRestrictionFamilies
