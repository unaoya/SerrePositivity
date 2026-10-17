module
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddleRestrictionKFlat
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullCalculation

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
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
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
