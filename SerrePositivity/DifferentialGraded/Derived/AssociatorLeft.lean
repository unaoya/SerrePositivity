module

public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.ModelIndependence
public import SerrePositivity.DifferentialGraded.Derived.Bimodule
public import SerrePositivity.DifferentialGraded.Derived.KFlat
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Restriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleComposition.Coherence

/-!
# Derived.AssociatorLeft

## 概要
18 本の同主題の構成と比較をまとめる。

## 方針
依存順に連結し、宣言と証明を保存する。

## 規約
元ごとの section で variable と option を保持する。private 名の変更は private_renames で明示する。

## 使われ方
DG の土台とその下流から import する。
-/

/-! ## KFlatBimoduleMiddleComparison（旧 SerrePositivity/DifferentialGraded/Derived/KFlatBimoduleMiddleComparison.lean） -/

/-! # 制限後の指定K-flatモデルを用いる導来中間比較

## 概要
制限後の指定K-flatモデルを用いる導来中間比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatBimoduleMiddleComparison
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] (F : DGFunctor A D C)
  (Q : RightKFlatBimoduleCategory A C E) (S : RightKFlatBimoduleCategory A D E)
  (q : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)

local notation "L" => derivedBimoduleRestriction A B D B C (DGFunctor.id B) F
local notation "KS" => rightKFlatDerivedCompose A B D E S
local notation "KQ" => rightKFlatDerivedCompose A B C E Q

/-- 固定モデルで合成するsourceの、前因子の局所化前での表示。 -/
def rightKFlatMiddleSourceBaseIso :
    bimoduleToDerived A B C ⋙ (L ⋙ KS) ≅
      BimoduleCategory.middleLeftRestrictionFunctor A B C D F ⋙
        composeWith A B D E S.obj ⋙ bimoduleToDerived A B E :=
  Functor.isoWhiskerRight (middleLeftRestrictionDerivedIso A B C D F).symm KS ≪≫
    Functor.isoWhiskerLeft (BimoduleCategory.middleLeftRestrictionFunctor A B C D F)
      (eqToIso (derivedComposeWith_fac A B D E S.obj S.property))

/-- 通常の指定増大による比較を前因子の局所化へ延長する前の自然変換。 -/
def rightKFlatMiddlePreComparison :
    bimoduleToDerived A B C ⋙ (L ⋙ KS) ⟶ bimoduleToDerived A B C ⋙ KQ :=
  (rightKFlatMiddleSourceBaseIso A B C D E F S).hom ≫
    whiskerRight (middleRestrictionResolvedNatTrans A B C D E F Q.obj S.obj q)
      (bimoduleToDerived A B E) ≫
    (eqToIso (derivedComposeWith_fac A B C E Q.obj Q.property)).inv

/-- 制限後のK-flat性を仮定せず、指定K-flatモデルの任意の増大を用いる導来比較。 -/
def rightKFlatMiddleComparison : L ⋙ KS ⟶ KQ := by
  letI sourceLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ (L ⋙ KS)) (L ⋙ KS) :=
    ⟨Iso.refl _⟩
  letI targetLifting : Localization.Lifting (bimoduleToDerived A B C)
      (BimoduleCategory.quasiIso A B C) (bimoduleToDerived A B C ⋙ KQ) KQ := ⟨Iso.refl _⟩
  exact Localization.liftNatTrans (bimoduleToDerived A B C) (BimoduleCategory.quasiIso A B C)
    (bimoduleToDerived A B C ⋙ (L ⋙ KS)) (bimoduleToDerived A B C ⋙ KQ)
    (L ⋙ KS) KQ (rightKFlatMiddlePreComparison A B C D E F Q S q)

/-- 元の前因子上で、入力制限表示の逆と通常の指定増大の比較へ計算する。 -/
lemma rightKFlatMiddleComparison_base_app (P : BimoduleCategory A B C) :
    (rightKFlatMiddleComparison A B C D E F Q S q).app ((bimoduleToDerived A B C).obj P) =
    (KS).map ((middleLeftRestrictionDerivedIso A B C D F).inv.app P) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj q) := by
  unfold rightKFlatMiddleComparison
  rw [Localization.liftNatTrans_app]
  simp only [rightKFlatMiddlePreComparison, rightKFlatMiddleSourceBaseIso,
    Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  change 𝟙 _ ≫ ((_ ≫ 𝟙 _) ≫ _ ≫ 𝟙 _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- 入力制限表示を前置すると、局所化した通常の比較を回復する。 -/
lemma rightKFlatMiddleComparison_base_square (P : BimoduleCategory A B C) :
    (KS).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P) ≫
      (rightKFlatMiddleComparison A B C D E F Q S q).app ((bimoduleToDerived A B C).obj P) =
    (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj q) := by
  rw [rightKFlatMiddleComparison_base_app, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end KFlatBimoduleMiddleComparison

/-! ## AssociatorLeftRestrictionBase（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionBase.lean） -/

/-! # 外側左制限比較の、元の前因子上での正規化計算

## 概要
外側左制限比較の、元の前因子上での正規化計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionBase
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)

/-- 固定K-flat後因子の左制限比較は、通常比較の局所化と既存制限表示で計算される。 -/
lemma derivedComposeWithLeftRestrictionIso_base_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
        (middleLeftRestrictionDerivedIso A B E D F).hom.app
          ((composeWith A B C E Q.obj).obj P) := by
  rw [derivedComposeWithLeftRestrictionIso_hom_app_calc]
  change 𝟙 _ ≫ _ ≫ _ ≫
      (derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionBase

/-! ## AssociatorLeftRestrictionKFlat（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionKFlat.lean） -/

/-! # 外側左制限は固定右K-flat因子の導来結合子を保つ

## 概要
外側左制限は固定右K-flat因子の導来結合子を保つ。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionKFlat
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "QLR" => rightKFlatCompose A C E D Q LR
local notation "LQR" => Functor.obj (rightKFlatLeftRestriction A C T D G) QR
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G

/-- 固定後二因子では、左制限の通常比較を導来合成へ送った射を通して結合子が可換。 -/
lemma rightKFlatDerivedAssociator_leftRestriction :
    (rightKFlatDerivedAssociator A B C E D Q LR).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom =
    whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithLeftRestrictionIso A B E T D G R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E T Q R).hom L := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [rightKFlatDerivedAssociator_base_app, rightKFlatDerivedMap_base_app,
    derivedComposeWithLeftRestrictionIso_base_app]
  let PQ := (composeWith A B C E Q.obj).obj P
  have hβ := derivedComposeWithLeftRestrictionIso_base_app A B E T D G R PQ
  erw [hβ, rightKFlatDerivedAssociator_base_app]
  let f := (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q.obj) (BimoduleCategory.underlying A E T R.obj)).hom
  have hn := (middleLeftRestrictionDerivedIso A B T D G).hom.naturality f
  have hs := congrArg ((bimoduleToDerived A B D).map)
    (associatorIso_leftRestriction A B C E T D G P Q.obj R.obj)
  simp only [CategoryTheory.Functor.map_comp] at hs
  have h := congrArg (fun k => k ≫
    (middleLeftRestrictionDerivedIso A B T D G).hom.app
      ((composeWith A B C T (QR).obj).obj P)) hs
  simp only [Category.assoc] at h
  erw [hn] at h
  simp only [Functor.comp_map] at h
  simp only [Category.assoc]
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionKFlat

/-! ## AssociatorLeftRestrictionPresentation（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionPresentation.lean） -/

/-! # 全導来外側左比較の逆を指定K-flatモデルへ計算する

## 概要
全導来外側左比較の逆を指定K-flatモデルへ計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionPresentation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (D : Type t) [DGCategory A D] [Small.{u} D] (F : DGFunctor A D E)
  (hE : localHomKFlat A E) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E)

local notation "LQ" => Functor.obj (rightKFlatLeftRestriction A C E D F) Q
local notation "L" => derivedBimoduleRestriction A B D B E (DGFunctor.id B) F

private lemma invert_model_square {V : Type*} [Category* V]
    {a b c d : V} (f : a ≅ b) (s : a ⟶ c) (t : b ⟶ d) (β : d ≅ c)
    (h : f.hom ≫ t = s ≫ β.inv) : f.inv ≫ s = t ≫ β.hom := by
  apply (Iso.cancel_iso_hom_left f _ _).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h]
  simp only [Category.assoc, β.inv_hom_id, Category.comp_id]

/-- 実際の全導来左比較の逆も、同じ指定モデルのsquareで計算される。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_model_square :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q =
    (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q ≫
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom := by
  exact invert_model_square
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).app
      ((bimoduleToDerived A C E).obj Q.obj)) _ _
    (derivedComposeWithLeftRestrictionIso A B C E D F Q)
    (derivedBimoduleComposeLeftRestrictionIso_model_square A B C E D F hE hD Q)

/-- source表示は、固定K-flat合成の表示を出力の左制限へ送ったもの。 -/
lemma leftRestrictionDerivedComposeSourceBaseIso_hom_app :
    (leftRestrictionDerivedComposeSourceBaseIso A B C E D F hE).hom.app Q =
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom L := by
  simp only [leftRestrictionDerivedComposeSourceBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- target表示は、後因子の制限表示の逆と、制限後K-flat因子の合成表示の合成。 -/
lemma leftRestrictionDerivedComposeTargetBaseIso_hom_app :
    (leftRestrictionDerivedComposeTargetBaseIso A B C E D F hD).hom.app Q =
      (derivedBimoduleComposeFunctor A B C D hD).map
          ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
        (derivedBimoduleComposeKFlatIso A B C D hD LQ).hom := by
  simp only [leftRestrictionDerivedComposeTargetBaseIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, whiskerRight_app,
    whiskerLeft_app, Iso.symm_hom, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- 全導来左比較の逆を、任意の導来前因子に自然な固定K-flat比較で計算する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation :
    (derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom L =
    (derivedBimoduleComposeFunctor A B C D hD).map
        ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj) ≫
      (derivedBimoduleComposeKFlatIso A B C D hD LQ).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C E D F Q).hom := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  simpa only [Category.assoc] using h

/-- 全導来左比較の逆を、前因子は任意のまま通常比較と既存表示で計算する。 -/
lemma derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
    (P : BimoduleCategory A B C) :
    ((derivedBimoduleComposeLeftRestrictionIso A B C E D F hE hD).inv.app
        ((bimoduleToDerived A C E).obj Q.obj)).app ((bimoduleToDerived A B C).obj P) ≫
      (L).map (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).hom =
    ((derivedBimoduleComposeFunctor A B C D hD).map
        ((middleLeftRestrictionDerivedIso A C E D F).inv.app Q.obj)).app
          ((bimoduleToDerived A B C).obj P) ≫
      (derivedBimoduleComposeKFlatValueIso A B C D hD LQ P).hom ≫
      (bimoduleToDerived A B D).map (composeLeftRestrictionIso A B C E D F P Q.obj).hom ≫
      (middleLeftRestrictionDerivedIso A B E D F).hom.app
        ((composeWith A B C E Q.obj).obj P) := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_model_square A B C E D F hE hD Q
  rw [leftRestrictionDerivedComposeSourceBaseIso_hom_app,
    leftRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  have hc := NatTrans.congr_app h ((bimoduleToDerived A B C).obj P)
  simp only [NatTrans.comp_app, whiskerRight_app,
    derivedComposeWithLeftRestrictionIso_base_app] at hc
  simpa only [derivedBimoduleComposeKFlatValueIso, Iso.app_hom, Category.assoc] using hc

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionPresentation

/-! ## AssociatorLeftRestrictionInner（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionInner.lean） -/

/-! # 外側左制限と導来結合子の内側合成のモデル比較

## 概要
外側左制限と導来結合子の内側合成のモデル比較。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionInner
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (C : Type v) [DGCategory A C] [Small.{u} C]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (D : Type t) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "L" => derivedBimoduleRestriction A C D C T (DGFunctor.id C) G

/-- 実際の全導来左比較は、内側合成の既存モデル表示と通常左制限比較に整合する。 -/
lemma derivedLeftRestriction_inner_model_square :
    ((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
        ((bimoduleToDerived A E T).obj R.obj)).app
          ((bimoduleToDerived A C E).obj Q.obj) ≫
      (L).map (derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom =
    (derivedBimoduleComposeInnerComparisonIso A C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      (bimoduleToDerived A C D).map
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (middleLeftRestrictionDerivedIso A C T D G).hom.app (QR).obj := by
  have h := derivedBimoduleComposeLeftRestrictionIso_inv_base_calculation
    A C E T D G hT hD R Q.obj
  simp only [derivedBimoduleComposeInnerComparisonIso, Iso.trans_hom, Iso.refl_hom,
    Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.assoc]
  convert h using 1
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionInner

/-! ## AssociatorLeftRestrictionNested（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionNested.lean） -/

/-! # 外側左制限と全導来結合子の入れ子側のモデルsquare

## 概要
外側左制限と全導来結合子の入れ子側のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionNested
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "QR" => rightKFlatCompose A C E T Q R
local notation "QLR" => rightKFlatCompose A C E D Q LR
local notation "LQR" => Functor.obj (rightKFlatLeftRestriction A C T D G) QR
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "LC" => derivedBimoduleRestriction A C D C T (DGFunctor.id C) G
local notation "HD" => derivedBimoduleComposeFunctor A B C D hD
local notation "U" => Functor.obj
  (Functor.obj (derivedBimoduleComposeFunctor A C E T hT)
    (Functor.obj (bimoduleToDerived A E T) R.obj))
  (Functor.obj (bimoduleToDerived A C E) Q.obj)
local notation "jT" => derivedBimoduleComposeInnerComparisonIso A C E T hT Q R
  (Iso.refl _) (Iso.refl _)

private lemma paste_nested {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d e : V} {x y z p q : W}
    (k : a ⟶ b) (u : b ⟶ c) (j : a ⟶ d) (g : d ⟶ e) (s : e ≅ c)
    (βb : H.obj b ⟶ x) (βc : H.obj c ⟶ y) (v : x ⟶ y)
    (out : y ⟶ z) (t : H.obj e ⟶ q) (r : H.obj d ⟶ p) (m : p ⟶ q) (β : q ⟶ z)
    (hi : k ≫ u = j ≫ g ≫ s.hom) (hn : H.map u ≫ βc = βb ≫ v)
    (hm : βc ≫ out = H.map s.inv ≫ t ≫ β) (hk : H.map g ≫ t = r ≫ m) :
    H.map k ≫ βb ≫ v ≫ out = H.map j ≫ r ≫ m ≫ β := by
  calc
    _ = H.map k ≫ H.map u ≫ βc ≫ out := by
      rw [← Category.assoc (H.map u) βc, hn, Category.assoc]
    _ = H.map (k ≫ u) ≫ βc ≫ out := by rw [H.map_comp, Category.assoc]
    _ = H.map j ≫ H.map g ≫ H.map s.hom ≫ βc ≫ out := by
      rw [hi, H.map_comp, H.map_comp]
      simp only [Category.assoc]
    _ = H.map j ≫ H.map g ≫ t ≫ β := by
      rw [hm, ← Category.assoc (H.map s.hom) (H.map s.inv),
        ← H.map_comp, s.hom_inv_id, H.map_id, Category.id_comp]
    _ = _ := by rw [← Category.assoc (H.map g) t, hk, Category.assoc]

/-- 内側モデルsquareと全導来比較の自然性を、入れ子表示の展開前に貼り合わせる。 -/
lemma derivedLeftRestriction_nested_prefix_square :
    (HD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U ≫
      whiskerRight ((derivedBimoduleComposeFunctor A B C T hT).map (jT).hom) L ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C T hT QR).hom L =
    (HD).map (derivedBimoduleComposeInnerComparisonIso A C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      (derivedBimoduleComposeKFlatIso A B C D hD QLR).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom := by
  have hi := derivedLeftRestriction_inner_model_square A C E T D G hT hD Q R
  have hn := (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.naturality
    (jT).hom
  have hm := derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation
    A B C T D G hT hD QR
  let g : QLR ⟶ LQR := ⟨(composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom⟩
  have hk := derivedBimoduleComposeKFlatIso_naturality A B C D hD g
  have h := paste_nested (HD) _ _ _ _
    ((middleLeftRestrictionDerivedIso A C T D G).app (QR).obj)
    _ _ _ _ _ _ _ _ hi hn hm hk
  convert h using 1 <;> rfl

/-- 全導来比較の入れ子側は、既存の入れ子表示を通して固定K-flatモデルの比較に戻る。 -/
lemma derivedLeftRestriction_nested_model_square :
    (HD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)).app ((bimoduleToDerived A C E).obj Q.obj)) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U ≫
      whiskerRight (derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
        (Iso.refl _) (Iso.refl _)).hom L =
    (derivedBimoduleComposeNestedComparisonIso A B C E D hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      rightKFlatDerivedMap A B C D (Q := QLR) (Q' := LQR)
        (composeLeftRestrictionIso A C E T D G Q.obj R.obj).hom ≫
      (derivedComposeWithLeftRestrictionIso A B C T D G QR).hom := by
  have h := derivedLeftRestriction_nested_prefix_square A B C E T D G hT hD Q R
  simpa only [derivedBimoduleComposeNestedComparisonIso, Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom, whiskerRight_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionNested

/-! ## AssociatorLeftRestrictionPair（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionPair.lean） -/

/-! # 外側左制限と全導来結合子の二段階合成側のモデルsquare

## 概要
外側左制限と全導来結合子の二段階合成側のモデルsquare。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionPair
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G

private lemma paste_pair {V W X : Type*} [Category* V] [Category* W] [Category* X]
    {U V' : V ⥤ W} (a : U ⟶ V') {S T K K' T' : W ⥤ X}
    (b : S ⟶ T) (out : T ⟶ T') (u : S ⟶ K) (v : K ⟶ K') (w : K' ⟶ T')
    (hm : b ≫ out = u ≫ v ≫ w) :
    whiskerLeft U b ≫ whiskerRight a T ≫ whiskerLeft V' out =
      whiskerLeft U u ≫ whiskerRight a K ≫ whiskerLeft V' v ≫ whiskerLeft V' w := by
  apply NatTrans.ext
  funext Y
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  have h := NatTrans.congr_app hm (V'.obj Y)
  simp only [NatTrans.comp_app] at h
  calc
    _ = S.map (a.app Y) ≫ b.app (V'.obj Y) ≫ out.app (V'.obj Y) := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ out.app (V'.obj Y)) (b.naturality (a.app Y)).symm
    _ = S.map (a.app Y) ≫ u.app (V'.obj Y) ≫ v.app (V'.obj Y) ≫ w.app (V'.obj Y) := by
      rw [h]
    _ = _ := by
      rw [← Category.assoc (S.map (a.app Y)) (u.app (V'.obj Y)), u.naturality,
        Category.assoc]

/-- 実際の全導来左比較は、二段階合成の表示を通すと固定モデルの比較に戻る。 -/
lemma derivedLeftRestriction_pair_model_square :
    whiskerLeft
        ((derivedBimoduleComposeFunctor A B C E hE).obj ((bimoduleToDerived A C E).obj Q.obj))
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app
          ((bimoduleToDerived A E T).obj R.obj)) ≫
      whiskerRight (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom L =
    (derivedBimoduleComposePairComparisonIso A B C E D hE hD Q LR (Iso.refl _)
        ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm).hom ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithLeftRestrictionIso A B E T D G R).hom := by
  have hm := derivedBimoduleComposeLeftRestrictionIso_inv_model_calculation
    A B E T D G hT hD R
  have h := paste_pair (derivedBimoduleComposeKFlatIso A B C E hE Q).hom
    _ _ _ _ _ hm
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom, Iso.symm_hom, Iso.app_inv,
      CategoryTheory.Functor.map_id, whiskerLeft_id', whiskerRight_id', whiskerRight_comp,
      Category.id_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionPair

/-! ## AssociatorLeftRestrictionModel（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionModel.lean） -/

/-! # 指定K-flat後二因子における全導来結合子と外側左制限

## 概要
指定K-flat後二因子における全導来結合子と外側左制限。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionModel
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "LR" => Functor.obj (rightKFlatLeftRestriction A E T D G) R
local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "LRD" => Functor.obj
  (derivedBimoduleRestriction A E D E T (DGFunctor.id E) G) RT
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT

private lemma post_paste {V W : Type*} [Category* V] [Category* W] (H : V ⥤ W)
    {a b c d : V} {x y : W} (α : a ⟶ b) (n : b ⟶ c) (p : a ⟶ d) (α' : d ⟶ c)
    (f : x ⟶ H.obj a) (s : x ⟶ y) (β : y ⟶ H.obj d)
    (ha : α ≫ n = p ≫ α') (hp : f ≫ H.map p = s ≫ β) :
    f ≫ H.map α ≫ H.map n = s ≫ β ≫ H.map α' := by
  have h := congrArg (fun k => f ≫ H.map k) ha
  simp only [H.map_comp] at h
  refine h.trans ?_
  simpa only [Category.assoc] using congrArg (fun k => k ≫ H.map α') hp

private lemma paste_associator {V : Type*} [Category* V]
    {a b c a' b' c' : V} (α : a ⟶ b) (β : b ⟶ c) (r : a ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (r' : a' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hr : r ≫ t.hom = s.hom ≫ r') (hm : α' ≫ β' = r') : α ≫ β = r := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = α ≫ n.hom ≫ β' := by rw [Category.assoc, hb]
    _ = s.hom ≫ α' ≫ β' := by rw [← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ r' := by rw [hm]
    _ = _ := hr.symm

/-- 後二因子を局所化した指定K-flatモデル上で、実際の全導来結合子が左制限と可換。 -/
lemma derivedBimoduleAssociator_leftRestriction_rightKFlat :
    (derivedBimoduleAssociator A B C E D hE hD QT LRD).hom ≫
      (derivedBimoduleComposeFunctor A B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app RT).app QT) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app U =
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app RT) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT QT RT).hom L := by
  let pD := derivedBimoduleComposePairComparisonIso A B C E D hE hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  let nD := derivedBimoduleComposeNestedComparisonIso A B C E D hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  let nT := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R (Iso.refl _) (Iso.refl _)
  have ha := derivedBimoduleAssociator_comparison_fac A B C E D hE hD Q LR (Iso.refl _)
    ((middleLeftRestrictionDerivedIso A E T D G).app R.obj).symm
  have hb := derivedLeftRestriction_nested_model_square A B C E T D G hT hD Q R
  have ht := derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  have hp := derivedLeftRestriction_pair_model_square A B C E T D G hE hT hD Q R
  have hr := post_paste ((whiskeringRight _ _ _).obj L) _ _ _ _ _ _ _ ht hp
  have hm := rightKFlatDerivedAssociator_leftRestriction A B C E T D G Q R
  exact paste_associator _ _ _ pD nD (Functor.isoWhiskerRight nT L) _ _ _ ha
    (by simpa only [Functor.isoWhiskerRight_hom, nD, nT, Category.assoc] using hb)
    (by simpa only [Functor.isoWhiskerRight_hom, whiskeringRight, pD, nT,
      Category.assoc] using hr) hm

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionModel

/-! ## AssociatorLeftRestrictionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionFamilies.lean） -/

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

@[expose] public section AssociatorLeftRestrictionFamilies
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorLeftRestrictionFamilies

/-! ## AssociatorLeftRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorLeftRestrictionCoherence.lean） -/

/-! # 全三因子に対する導来結合子と外側左制限のcoherence

## 概要
全三因子に対する導来結合子と外側左制限のcoherence。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorLeftRestrictionCoherence
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (D : Type s) [DGCategory A D] [Small.{u} D] (G : DGFunctor A D T)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T) (hD : localHomKFlat A D)

local notation "L" => derivedBimoduleRestriction A B D B T (DGFunctor.id B) G
local notation "LE" => derivedBimoduleRestriction A E D E T (DGFunctor.id E) G

/-- モデル上の一致を後二つの全導来変数へ持ち上げた、関手族間の経路の一致。 -/
lemma leftRestrictionAssociatorPaths_eq :
    leftRestrictionAssociatorLeftPath A B C E T D G hE hT hD =
      leftRestrictionAssociatorRightPath A B C E T D G hE hT hD := by
  apply rightKFlatDerivedNatTrans_ext A E T hT
  intro R
  apply rightKFlatDerivedNatTrans_ext A C E hE
  intro Q
  rw [leftRestrictionAssociatorLeftPath_app, leftRestrictionAssociatorRightPath_app]
  exact derivedBimoduleAssociator_leftRestriction_rightKFlat A B C E T D G hE hT hD Q R

/-- 任意の全導来後二因子と任意の導来前因子について、外側左制限が結合子を保つ。 -/
lemma derivedBimoduleAssociator_leftRestriction
    (Q : DerivedBimoduleCategory A C E) (R : DerivedBimoduleCategory A E T) :
    (derivedBimoduleAssociator A B C E D hE hD Q ((LE).obj R)).hom ≫
      (derivedBimoduleComposeFunctor A B C D hD).map
        (((derivedBimoduleComposeLeftRestrictionIso A C E T D G hT hD).inv.app R).app Q) ≫
      (derivedBimoduleComposeLeftRestrictionIso A B C T D G hT hD).inv.app
        (((derivedBimoduleComposeFunctor A C E T hT).obj R).obj Q) =
    whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj Q)
        ((derivedBimoduleComposeLeftRestrictionIso A B E T D G hT hD).inv.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom L := by
  have h := NatTrans.congr_app
    (NatTrans.congr_app (leftRestrictionAssociatorPaths_eq A B C E T D G hE hT hD) R) Q
  simpa only [leftRestrictionAssociatorLeftPath_app,
    leftRestrictionAssociatorRightPath_app] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorLeftRestrictionCoherence

/-! ## AssociatorRightRestrictionBase（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionBase.lean） -/

/-! # 外側右制限比較の局所化前の計算

## 概要
外側右制限比較の局所化前の計算。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionBase
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)

/-- 入力側の制限表示の逆、通常比較の局所化、出力側の制限表示による計算。 -/
lemma derivedComposeWithRightRestrictionIso_base_app
    (Q : RightKFlatBimoduleCategory A C E) (P : BimoduleCategory A B C) :
    (derivedComposeWithRightRestrictionIso A B D C E F Q).hom.app
        ((bimoduleToDerived A B C).obj P) =
      (rightKFlatDerivedCompose A D C E Q).map
          ((middleRightRestrictionDerivedIso A B D F C).inv.app P) ≫
        (bimoduleToDerived A D E).map (composeRightRestrictionIso A B D C E F P Q.obj).hom ≫
        (middleRightRestrictionDerivedIso A B D F E).hom.app
          ((composeWith A B C E Q.obj).obj P) := by
  rw [derivedComposeWithRightRestrictionIso_hom_app_calc]
  change _ ≫ 𝟙 _ ≫ _ ≫ _ ≫
    (derivedBimoduleRestriction A D E B E F (DGFunctor.id E)).map (𝟙 _) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

private lemma post_square {V : Type*} [Category* V] {a b c d e x y : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : a ⟶ d) (δ : d ⟶ e) (ε : e ⟶ c)
    (s : c ⟶ x) (t : e ⟶ y) (f : y ⟶ x)
    (h : α ≫ β = γ ≫ δ ≫ ε) (hn : ε ≫ s = t ≫ f) :
    α ≫ β ≫ s = γ ≫ δ ≫ t ≫ f := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [hn]

variable (T : Type s) [DGCategory A T] [Small.{u} T]

/-- 通常の結合子squareを局所化し、出力の既存右制限表示を続けた式。 -/
lemma associatorRightRestriction_localized_square
    (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
    (R : BimoduleCategory A E T) :
    (bimoduleToDerived A D T).map
        (associatorIso A D C E T
          (Bimodule.rightRestriction A B D C F (BimoduleCategory.underlying A B C P))
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom ≫
      (bimoduleToDerived A D T).map (composeRightRestrictionIso A B D C T F P
        (BimoduleCategory.of A C T (compose A C E T
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)))).hom ≫
      (middleRightRestrictionDerivedIso A B D F T).hom.app
        ((composeWith A B C T (BimoduleCategory.of A C T (compose A C E T
          (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)))).obj P) =
    (bimoduleToDerived A D T).map
        (composeMap A D E T (composeRightRestrictionIso A B D C E F P Q).hom (𝟙 R)) ≫
      (bimoduleToDerived A D T).map (composeRightRestrictionIso A B D E T F
        ((composeWith A B C E Q).obj P) R).hom ≫
      (middleRightRestrictionDerivedIso A B D F T).hom.app
        ((composeWith A B E T R).obj ((composeWith A B C E Q).obj P)) ≫
      (derivedBimoduleRestriction A D T B T F (DGFunctor.id T)).map
        ((bimoduleToDerived A B T).map
          (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
            (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom) := by
  let f := (associatorIso A B C E T (BimoduleCategory.underlying A B C P)
    (BimoduleCategory.underlying A C E Q) (BimoduleCategory.underlying A E T R)).hom
  have hn := (middleRightRestrictionDerivedIso A B D F T).hom.naturality f
  have hs := congrArg ((bimoduleToDerived A D T).map)
    (associatorIso_rightRestriction A B D C E T F P Q R)
  simp only [CategoryTheory.Functor.map_comp] at hs
  simp only [Functor.comp_map] at hn
  exact post_square _ _ _ _ _ _ _ _ hs hn

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionBase

/-! ## AssociatorRightRestrictionKFlat（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionKFlat.lean） -/

/-! # 外側右制限は固定右K-flat因子の導来結合子を保つ

## 概要
外側右制限は固定右K-flat因子の導来結合子を保つ。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionKFlat
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QR" => rightKFlatCompose A C E T Q R

/-- 任意の導来前因子に自然な、外側右制限と固定K-flat結合子の可換square。 -/
lemma rightKFlatDerivedAssociator_rightRestriction :
    whiskerLeft RI (rightKFlatDerivedAssociator A D C E T Q R).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C T F QR).hom =
    whiskerRight (derivedComposeWithRightRestrictionIso A B D C E F Q).hom
        (rightKFlatDerivedCompose A D E T R) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithRightRestrictionIso A B D E T F R).hom ≫
      whiskerRight (rightKFlatDerivedAssociator A B C E T Q R).hom RO := by
  apply bimoduleDerivedNatTrans_ext A B C
  intro P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [derivedComposeWithRightRestrictionIso_base_app,
    derivedComposeWithRightRestrictionIso_base_app]
  let PQ := (composeWith A B C E Q.obj).obj P
  have hβ := derivedComposeWithRightRestrictionIso_base_app A B D E T F R PQ
  have hαB := rightKFlatDerivedAssociator_base_app A B C E T Q R P
  erw [hβ, hαB]
  have ha := (rightKFlatDerivedAssociator A D C E T Q R).hom.naturality
    ((middleRightRestrictionDerivedIso A B D F C).inv.app P)
  simp only [Functor.comp_map] at ha
  simp only [Category.assoc]
  have hαD := rightKFlatDerivedAssociator_base_app A D C E T Q R
    ((BimoduleCategory.middleRightRestrictionFunctor A B D C F).obj P)
  rw [← reassoc_of% ha]
  erw [hαD]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hc := ((rightKFlatDerivedCompose A D E T R).mapIso
    ((middleRightRestrictionDerivedIso A B D F E).app PQ)).hom_inv_id
  simp only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv] at hc
  rw [reassoc_of% hc]
  have hmap := rightKFlatDerivedCompose_map_base A D E T R
    (composeRightRestrictionIso A B D C E F P Q.obj).hom
  rw [hmap]
  have h := associatorRightRestriction_localized_square A B D C E F T P Q.obj R.obj
  have hh := congrArg (fun k =>
    (rightKFlatDerivedCompose A D E T R).map
      ((rightKFlatDerivedCompose A D C E Q).map
        ((middleRightRestrictionDerivedIso A B D F C).inv.app P)) ≫ k) h
  convert hh using 1
  rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionKFlat

/-! ## AssociatorRightRestrictionPresentation（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionPresentation.lean） -/

/-! # 外側右制限の全導来比較を固定K-flat合成の表示へ計算する

## 概要
外側右制限の全導来比較を固定K-flat合成の表示へ計算する。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionPresentation
universe u v w z t

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D E B E F (DGFunctor.id E)

lemma rightRestrictionDerivedComposeSourceBaseIso_hom_app :
    (rightRestrictionDerivedComposeSourceBaseIso A B D C E F hE).hom.app Q =
      whiskerLeft RI (derivedBimoduleComposeKFlatIso A D C E hE Q).hom := by
  simp only [rightRestrictionDerivedComposeSourceBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

lemma rightRestrictionDerivedComposeTargetBaseIso_hom_app :
    (rightRestrictionDerivedComposeTargetBaseIso A B D C E F hE).hom.app Q =
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom RO := by
  simp only [rightRestrictionDerivedComposeTargetBaseIso, Functor.isoWhiskerRight_hom,
    whiskerRight_app, rightKFlatComposePresentationIso_hom_app]
  rfl

/-- 全導来右比較と固定K-flat右比較を結ぶ、任意の導来前因子に自然なsquare。 -/
lemma derivedBimoduleComposeRightRestrictionIso_model_calculation :
    (derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app
        ((bimoduleToDerived A C E).obj Q.obj) ≫
      whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE Q).hom RO =
    whiskerLeft RI (derivedBimoduleComposeKFlatIso A D C E hE Q).hom ≫
      (derivedComposeWithRightRestrictionIso A B D C E F Q).hom := by
  have h := derivedBimoduleComposeRightRestrictionIso_model_square A B D C E F hE Q
  rw [rightRestrictionDerivedComposeSourceBaseIso_hom_app,
    rightRestrictionDerivedComposeTargetBaseIso_hom_app] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionPresentation

/-! ## AssociatorRightRestrictionNested（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionNested.lean） -/

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

@[expose] public section AssociatorRightRestrictionNested
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorRightRestrictionNested

/-! ## AssociatorRightRestrictionPair（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionPair.lean） -/

/-! # 外側右制限と二段階全導来合成の表示

## 概要
外側右制限と二段階全導来合成の表示。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionPair
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj

private lemma paste_horizontal {V W X : Type*} [Category* V] [Category* W] [Category* X]
    (U : W ⥤ V) (H K : V ⥤ X) (J L : W ⥤ X)
    (b : U ⋙ H ⟶ J) (b' : U ⋙ K ⟶ L) (k : H ⟶ K) (l : J ⟶ L)
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
    _ = H.map a ≫ H.map (U.map v) ≫ b.app y' ≫ l.app y' := by
      rw [← reassoc_of% hn]
    _ = H.map w ≫ H.map a' ≫ b.app y' ≫ l.app y' := by
      rw [← Category.assoc (H.map a), hm, Category.assoc]
    _ = H.map w ≫ H.map a' ≫ k.app (U.obj y') ≫ b'.app y' := by rw [hc]
    _ = _ := by rw [← reassoc_of% (k.naturality a')]

/-- 二段階の全導来右比較は、両側の合成表示を通すと固定K-flat比較に戻る。 -/
lemma derivedRightRestriction_pair_model_square :
    whiskerRight
        ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT) ≫
      whiskerRight (derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom RO =
    whiskerLeft RI (derivedBimoduleComposePairComparisonIso A D C E T hE hT Q R
        (Iso.refl _) (Iso.refl _)).hom ≫
      whiskerRight (derivedComposeWithRightRestrictionIso A B D C E F Q).hom
        (rightKFlatDerivedCompose A D E T R) ≫
      whiskerLeft (rightKFlatDerivedCompose A B C E Q)
        (derivedComposeWithRightRestrictionIso A B D E T F R).hom := by
  apply NatTrans.ext
  funext P
  have hq := NatTrans.congr_app
    (derivedBimoduleComposeRightRestrictionIso_model_calculation A B D C E F hE Q) P
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hq
  have hr := derivedBimoduleComposeRightRestrictionIso_model_calculation A B D E T F hT R
  have h := paste_horizontal _ _ _ _ _ _ _ _ _ hr _ _ _ _ hq
  convert h using 1 <;>
    simp only [derivedBimoduleComposePairComparisonIso, Iso.trans_hom,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, whiskerLeft_id', whiskerRight_id',
      NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.id_comp,
      CategoryTheory.Functor.map_comp, Category.assoc]
  all_goals rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionPair

/-! ## AssociatorRightRestrictionModel（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionModel.lean） -/

/-! # 指定K-flat後二因子における全導来結合子と外側右制限

## 概要
指定K-flat後二因子における全導来結合子と外側右制限。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionModel
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)
  (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A E T)

local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "QT" => Functor.obj (bimoduleToDerived A C E) Q.obj
local notation "RT" => Functor.obj (bimoduleToDerived A E T) R.obj
local notation "U" => Functor.obj (Functor.obj (derivedBimoduleComposeFunctor A C E T hT) RT) QT

private lemma paste_rectangle {V : Type*} [Category* V] {a b c d a' b' c' d' : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : a ⟶ d) (δ : d ⟶ c)
    (s : a ≅ a') (n : b ≅ b') (t : c ≅ c') (m : d ≅ d')
    (α' : a' ⟶ b') (β' : b' ⟶ c') (γ' : a' ⟶ d') (δ' : d' ⟶ c')
    (ha : α ≫ n.hom = s.hom ≫ α') (hb : β ≫ t.hom = n.hom ≫ β')
    (hc : γ ≫ m.hom = s.hom ≫ γ') (hd : δ ≫ t.hom = m.hom ≫ δ')
    (hm : α' ≫ β' = γ' ≫ δ') : α ≫ β = γ ≫ δ := by
  apply (Iso.cancel_iso_hom_right _ _ t).1
  calc
    _ = s.hom ≫ α' ≫ β' := by rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]
    _ = s.hom ≫ γ' ≫ δ' := by rw [hm]
    _ = (γ ≫ δ) ≫ t.hom := by
      rw [Category.assoc γ δ t.hom, hd, ← Category.assoc γ, hc, Category.assoc]

/-- 指定右K-flatモデルを局所化した後二因子で、実際の全導来結合子が右制限と可換。 -/
lemma derivedBimoduleAssociator_rightRestriction_rightKFlat :
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT QT RT).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app U =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT QT RT).hom RO := by
  let pD := derivedBimoduleComposePairComparisonIso A D C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nD := derivedBimoduleComposeNestedComparisonIso A D C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  let pB := derivedBimoduleComposePairComparisonIso A B C E T hE hT Q R
    (Iso.refl _) (Iso.refl _)
  let nB := derivedBimoduleComposeNestedComparisonIso A B C E T hT Q R
    (Iso.refl _) (Iso.refl _)
  have ha := congrArg (fun k => whiskerLeft RI k)
    (derivedBimoduleAssociator_comparison_fac A D C E T hE hT Q R
      (Iso.refl _) (Iso.refl _))
  have hd := congrArg (fun k => whiskerRight k RO)
    (derivedBimoduleAssociator_comparison_fac A B C E T hE hT Q R
      (Iso.refl _) (Iso.refl _))
  simp only [whiskerLeft_comp] at ha
  simp only [whiskerRight_comp] at hd
  have hb := derivedRightRestriction_nested_model_square A B D C E T F hT Q R
  have hc := derivedRightRestriction_pair_model_square A B D C E T F hE hT Q R
  have hm := rightKFlatDerivedAssociator_rightRestriction A B D C E T F Q R
  simpa only [Category.assoc] using paste_rectangle _ _
    (whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app QT)
        ((derivedBimoduleComposeFunctor A D E T hT).obj RT) ≫
      whiskerLeft ((derivedBimoduleComposeFunctor A B C E hE).obj QT)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app RT)) _
    (Functor.isoWhiskerLeft RI pD)
    (Functor.isoWhiskerLeft RI nD) (Functor.isoWhiskerRight nB RO)
    (Functor.isoWhiskerRight pB RO) _ _ _ _ ha hb
    (by simpa only [Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      pD, pB, Category.assoc] using hc) hd
    (by simpa only [Category.assoc] using hm)

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionModel

/-! ## AssociatorRightRestrictionFamilies（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionFamilies.lean） -/

/-! # 外側右制限と結合子の両経路の全三変数自然性

## 概要
外側右制限と結合子の両経路の全三変数自然性。

## 方針
既存の制限表示と指定K-flatモデルの計算を局所化へ移し、実際の比較射の経路を照合する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。U16dで指定の制限squareを使う際の候補。一般Morita・tensor・
Hochschild型構成のモデル比較にも利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section AssociatorRightRestrictionFamilies
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (C : Type z) [DGCategory A C] [Small.{u} C]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] [Small.{u} T] (F : DGFunctor A D B)
  (hE : localHomKFlat A E) (hT : localHomKFlat A T)

local notation "X" => DerivedBimoduleCategory A B C
local notation "XD" => DerivedBimoduleCategory A D C
local notation "Y" => DerivedBimoduleCategory A C E
local notation "Z" => DerivedBimoduleCategory A E T
local notation "W" => DerivedBimoduleCategory A D T
local notation "V" => DerivedBimoduleCategory A B T
local notation "DE" => DerivedBimoduleCategory A D E
local notation "BE" => DerivedBimoduleCategory A B E
local notation "RI" => derivedBimoduleRestriction A D C B C F (DGFunctor.id C)
local notation "RO" => derivedBimoduleRestriction A D T B T F (DGFunctor.id T)
local notation "HBQ" => derivedBimoduleComposeFunctor A B C E hE
local notation "HDR" => derivedBimoduleComposeFunctor A D E T hT
local notation "HR" => derivedBimoduleComposeFunctor A C E T hT
local notation "βQ" => Iso.hom (derivedBimoduleComposeRightRestrictionIso A B D C E F hE)
local notation "βR" => Iso.hom (derivedBimoduleComposeRightRestrictionIso A B D E T F hT)

/-- 前因子を右制限してから二段階合成する全三変数の関手族。 -/
def rightRestrictionAssociatorSource : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorSource A D C E T hE hT ⋙
    (whiskeringRight Y (XD ⥤ W) (X ⥤ W)).obj ((whiskeringLeft X XD W).obj RI)

/-- 三因子の合成後に外側右制限を適用する、両経路共通の関手族。 -/
def rightRestrictionAssociatorTarget : Z ⥤ Y ⥤ X ⥤ W :=
  derivedBimoduleAssociatorTarget A B C E T hT ⋙
    (whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj RO)

/-- 全導来結合子と入れ子合成の右制限比較を続ける経路。 -/
def rightRestrictionAssociatorLeftPath :
    rightRestrictionAssociatorSource A B D C E T F hE hT ⟶
      rightRestrictionAssociatorTarget A B D C E T F hT :=
  whiskerRight (derivedBimoduleAssociatorIso A D C E T hE hT).hom
      ((whiskeringRight Y (XD ⥤ W) (X ⥤ W)).obj ((whiskeringLeft X XD W).obj RI)) ≫
    whiskerLeft HR ((whiskeringRight Y (DerivedBimoduleCategory A C T) (X ⥤ W)).map
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom)

/-- 二段階の右制限比較と元の全導来結合子を続ける経路。 -/
def rightRestrictionAssociatorRightPath :
    rightRestrictionAssociatorSource A B D C E T F hE hT ⟶
      rightRestrictionAssociatorTarget A B D C E T F hT :=
  whiskerLeft (HDR ⋙ whiskeringRight X DE W)
      ((whiskeringLeft Y (X ⥤ DE) (X ⥤ W)).map βQ) ≫
    whiskerRight βR (whiskeringRight X BE W ⋙
      (whiskeringLeft Y (X ⥤ BE) (X ⥤ W)).obj HBQ) ≫
    whiskerRight (derivedBimoduleAssociatorIso A B C E T hE hT).hom
      ((whiskeringRight Y (X ⥤ V) (X ⥤ W)).obj ((whiskeringRight X V W).obj RO))

lemma rightRestrictionAssociatorLeftPath_app (Q : Y) (R : Z) :
    ((rightRestrictionAssociatorLeftPath A B D C E T F hE hT).app R).app Q =
    whiskerLeft RI (derivedBimoduleAssociator A D C E T hE hT Q R).hom ≫
      (derivedBimoduleComposeRightRestrictionIso A B D C T F hT).hom.app
        (((HR).obj R).obj Q) := rfl

lemma rightRestrictionAssociatorRightPath_app (Q : Y) (R : Z) :
    ((rightRestrictionAssociatorRightPath A B D C E T F hE hT).app R).app Q =
    whiskerRight ((derivedBimoduleComposeRightRestrictionIso A B D C E F hE).hom.app Q)
        ((HDR).obj R) ≫
      whiskerLeft ((HBQ).obj Q)
        ((derivedBimoduleComposeRightRestrictionIso A B D E T F hT).hom.app R) ≫
      whiskerRight (derivedBimoduleAssociator A B C E T hE hT Q R).hom RO := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end AssociatorRightRestrictionFamilies

/-! ## AssociatorRightRestrictionCoherence（旧 SerrePositivity/DifferentialGraded/Derived/AssociatorRightRestrictionCoherence.lean） -/

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

@[expose] public section AssociatorRightRestrictionCoherence
universe u v w z t s

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
end

end AssociatorRightRestrictionCoherence
