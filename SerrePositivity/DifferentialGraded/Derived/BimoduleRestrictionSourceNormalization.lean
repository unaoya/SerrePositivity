module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleFullCalculation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRightRestrictionFull
public import SerrePositivity.DifferentialGraded.Derived.BimoduleRestrictionModelCalculation

/-! # 外側右制限と中間比較のsource表示の正規化

## 概要
外側右制限と中間比較のsource表示の正規化。

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
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (K : Type s) [DGCategory A K] [Small.{u} K] (G : DGFunctor A K B)
  (hE : localHomKFlat A E) (P : BimoduleCategory A B C)
  (Q : RightKFlatBimoduleCategory A C E)

local notation "LP" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B C D F) P
local notation "GP" => Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A B K D G) LP
local notation "RQ₀" => Functor.obj (bimoduleToDerived A D E)
  (Functor.obj (BimoduleCategory.middleRightRestrictionFunctor A C D E F) Q.obj)
local notation "RQ₁" => Functor.obj
  (derivedBimoduleRestriction A D E C E F (DGFunctor.id E))
  (Functor.obj (bimoduleToDerived A C E) Q.obj)
local notation "HK" => derivedBimoduleComposeFunctor A K D E hE
local notation "HB" => derivedBimoduleComposeFunctor A B D E hE
local notation "RG" => derivedBimoduleRestriction A K E B E G (DGFunctor.id E)

/-- 後因子の制限表示から、外側比較を経て前因子の左制限表示へ進む実際のsource経路。 -/
def restrictedMiddleSourcePrefix :=
  ((HK).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)).app
      ((bimoduleToDerived A K D).obj GP) ≫
    ((HK).obj RQ₁).map ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
    ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app RQ₁).app
      ((bimoduleToDerived A B D).obj LP) ≫
    (RG).map (((HB).obj RQ₁).map ((middleLeftRestrictionDerivedIso A B C D F).hom.app P))

private lemma paste_source_squares {V : Type*} [Category* V]
    {a b c d e f g h : V} (r : a ⟶ b) (p : b ⟶ c) (β : c ⟶ d) (u : d ⟶ h)
    (p₀ : a ⟶ e) (r' : e ⟶ c) (β₀ : e ⟶ f) (v : f ⟶ d) (u₀ : f ⟶ g) (v' : g ⟶ h)
    (h₁ : r ≫ p = p₀ ≫ r') (h₂ : r' ≫ β = β₀ ≫ v) (h₃ : v ≫ u = u₀ ≫ v') :
    r ≫ p ≫ β ≫ u = p₀ ≫ β₀ ≫ u₀ ≫ v' := by
  rw [← Category.assoc r p, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc r' β, h₂]
  simp only [Category.assoc]
  rw [h₃]

/-- 後因子の制限表示を外側比較の自然性で移すと、既存の中間source表示に一致する。 -/
lemma restrictedMiddleSourcePrefix_normalize :
    restrictedMiddleSourcePrefix A B C D E F K G hE P Q =
      ((HK).obj RQ₀).map ((middleRightRestrictionDerivedIso A B K G D).hom.app LP) ≫
      ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.app RQ₀).app
        ((bimoduleToDerived A B D).obj LP) ≫
      (RG).map ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P) := by
  let r := (HK).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)
  let v := (HB).map ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj)
  let p := (middleRightRestrictionDerivedIso A B K G D).hom.app LP
  let u := (middleLeftRestrictionDerivedIso A B C D F).hom.app P
  have h₁ := (r.naturality p).symm
  have h₂ := NatTrans.congr_app
    ((derivedBimoduleComposeRightRestrictionIso A B K D E G hE).hom.naturality
      ((middleRightRestrictionDerivedIso A C D F E).hom.app Q.obj))
    ((bimoduleToDerived A B D).obj LP)
  simp only [NatTrans.comp_app] at h₂
  have h₃ := congrArg (RG).map (v.naturality u).symm
  simp only [CategoryTheory.Functor.map_comp] at h₃
  rw [middleDerivedSourceFamilyIdentification_hom_app_calc, CategoryTheory.Functor.map_comp]
  exact paste_source_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃

/-- source正規化を任意の指定解像度の計算同型へ接続した式。 -/
lemma restrictedMiddleSourcePrefix_model
    (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    (derivedBimoduleComposeResolutionComputation A K D E hE
        ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).inv.app
        ((bimoduleToDerived A K D).obj GP) ≫
      restrictedMiddleSourcePrefix A B C D E F K G hE P Q =
    restrictedMiddleModelPrefix A B C D E F K G hE P Q R q hq ≫
      (RG).map ((middleDerivedSourceFamilyIdentification A B C D E F hE Q).hom.app P) := by
  have h := congrArg (fun k =>
    (derivedBimoduleComposeResolutionComputation A K D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj) R q hq).inv.app
      ((bimoduleToDerived A K D).obj GP) ≫ k)
    (restrictedMiddleSourcePrefix_normalize A B C D E F K G hE P Q)
  simpa only [restrictedMiddleModelPrefix, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
