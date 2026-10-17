module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIndependence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionValueNaturality

/-! # 増大squareから導く中間圏導来比較の後因子自然性

## 概要
増大squareから導く中間圏導来比較の後因子自然性。

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

lemma derivedMiddleRestrictionComparison_second_naturality_of_squares (hE : localHomKFlat A E)
    {Q Q' : RightKFlatBimoduleCategory A C E} (g : Q ⟶ Q')
    (R S : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (s : S.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q'.obj)
    (hq : BimoduleCategory.quasiIso A D E q) (hs : BimoduleCategory.quasiIso A D E s)
    (r : R ⟶ S)
    (h₀ : (bimoduleToDerived A D E).map q ≫
        (bimoduleToDerived A D E).map (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom) =
      (bimoduleToDerived A D E).map r.hom ≫ (bimoduleToDerived A D E).map s)
    (P : BimoduleCategory A B C)
    (h₁ : (bimoduleToDerived A B E).map (composeMap A B D E (𝟙 (BimoduleCategory.of A B D
        (Bimodule.leftRestriction A B C D F (BimoduleCategory.underlying A B C P)))) r.hom) ≫
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q'.obj S.obj s) =
      (bimoduleToDerived A B E).map (middleRestrictionResolvedMap A B C D E F P Q.obj R.obj q) ≫
        (bimoduleToDerived A B E).map (composeMap A B C E (𝟙 P) g.hom)) :
    ((derivedBimoduleComposeFunctor A B D E hE).map ((bimoduleToDerived A D E).map
        (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P)) ≫
      derivedMiddleRestrictionComparison A B C D E F hE P Q' S s hs =
    derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq ≫
      ((derivedBimoduleComposeFunctor A B C E hE).map ((bimoduleToDerived A C E).map g.hom)).app
        ((bimoduleToDerived A B C).obj P) := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B C D F).obj P
  have hσ := derivedBimoduleComposeResolutionValueIso_naturality A B D E hE R S q s hq hs
    (BimoduleCategory.middleRightRestrictionMap A C D E F g.hom) r h₀ P₀
  have hτ := derivedBimoduleComposeKFlatValueIso_naturality A B C E hE g P
  apply (Iso.cancel_iso_hom_right _ _ (derivedBimoduleComposeKFlatValueIso A B C E hE Q' P)).1
  dsimp only [derivedMiddleRestrictionComparison]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hτ, Iso.inv_hom_id_assoc]
  change _ ≫ (middleRestrictionSourceComputation A B C D E F hE P Q'.obj S s hs).hom =
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ _ at hσ
  have he := congrArg (fun k => k ≫ (bimoduleToDerived A B E).map
    (middleRestrictionResolvedMap A B C D E F P Q'.obj S.obj s)) hσ
  have hf := congrArg (fun k =>
    (middleRestrictionSourceComputation A B C D E F hE P Q.obj R q hq).hom ≫ k) h₁
  exact (Category.assoc _ _ _).symm.trans
    (he.trans ((Category.assoc _ _ _).trans hf))

end SerrePositivity.DifferentialGraded.BimoduleTensor
