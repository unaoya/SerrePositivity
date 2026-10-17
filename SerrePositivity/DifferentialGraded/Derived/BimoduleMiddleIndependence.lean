module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparisonLocalization
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleHomotopy
public import SerrePositivity.DifferentialGraded.Derived.BimoduleSourceHomotopy
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionResolutionValues

/-! # 中間圏の導来比較射の解像度変更に関する整合性

## 概要
中間圏の導来比較射の解像度変更に関する整合性。

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
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D C)
  (hE : localHomKFlat A E) (Q : RightKFlatBimoduleCategory A C E)
  (R S : RightKFlatBimoduleCategory A D E)
  (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (s : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
  (hq : BimoduleCategory.quasiIso A D E q) (hs : BimoduleCategory.quasiIso A D E s)

/-- 増大squareと合成後の計算squareが導来可換なら、実際の比較射は一致する。 -/
lemma derivedMiddleRestrictionComparison_eq_of_squares (r : R ⟶ S)
    (h₀ : (bimoduleToDerived A D E).map q =
      (bimoduleToDerived A D E).map r.hom ≫ (bimoduleToDerived A D E).map s)
    (P : BimoduleCategory A B C)
    (h₁ : (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj S.obj s) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q)) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q S s hs =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  have hc : (middleRestrictionSourceComputation A B C D E F hE P Q.obj S s hs).hom =
      (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫
        (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
          (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) :=
    derivedBimoduleComposeResolutionValueIso_change A B D E hE _ R S q s hq hs r h₀ _
  dsimp only [derivedMiddleRestrictionComparison]
  rw [hc]
  have he := congrArg (fun k =>
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ k ≫
      (derivedBimoduleComposeKFlatValueIso A B C E hE Q P).inv) h₁
  simpa only [Category.assoc] using he

/-- 増大squareが積dg圏表示の主Kで可換なら、指定解像度による導来比較は一致する。 -/
lemma derivedMiddleRestrictionComparison_eq_of_source_homotopy (r : R ⟶ S)
    (h : (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map (r.hom ≫ s)) =
      (moduleToHomotopy A (DGTensorCategory A Dᵒᵖ E)ᵒᵖ).map
        ((rightModuleBimoduleEquivalence A D E).inverse.map q)) (P : BimoduleCategory A B C) :
    derivedMiddleRestrictionComparison A B C D E F hE P Q S s hs =
      derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq := by
  have h₀ := bimoduleDerived_map_eq_of_inverse_source_homotopy A D E (r.hom ≫ s) q h
  rw [CategoryTheory.Functor.map_comp] at h₀
  exact derivedMiddleRestrictionComparison_eq_of_squares A B C D E F hE Q R S q s hq hs r
    h₀.symm P (middleRestrictionResolvedMap_comp_of_source_homotopy A B C D E F
      P Q.obj q s r.hom h)

end SerrePositivity.DifferentialGraded.BimoduleTensor
