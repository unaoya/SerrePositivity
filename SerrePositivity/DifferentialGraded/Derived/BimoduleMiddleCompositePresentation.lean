module
public import SerrePositivity.DifferentialGraded.Derived.MiddleRestrictionIteratedPresentation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleCompositeFamily

/-! # 二段階中間比較の閉零表示と合成正規化の可換性

## 概要
二段階中間比較の閉零表示と合成正規化の可換性。

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

private lemma bifunctor_square
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : C ⥤ D ⥤ E)
    {r₀ r₁ r₂ r₃ : C} {l₀ l₁ l₂ l₃ : D}
    (a : r₀ ⟶ r₁) (b : r₁ ⟶ r₂) (c : r₀ ⟶ r₃) (d : r₃ ⟶ r₂)
    (x : l₀ ⟶ l₁) (y : l₁ ⟶ l₂) (z : l₀ ⟶ l₃) (w : l₃ ⟶ l₂)
    (hr : a ≫ b = c ≫ d) (hl : x ≫ y = z ≫ w) :
    (H.obj r₀).map x ≫ (H.map a).app l₁ ≫ (H.map b).app l₁ ≫ (H.obj r₂).map y =
      (H.map c).app l₀ ≫ (H.obj r₃).map z ≫ (H.obj r₃).map w ≫ (H.map d).app l₂ := by
  have hn := (H.map (a ≫ b)).naturality y
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc] at hn
  calc
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (a ≫ b)).app l₂ := by
      simpa only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
        using congrArg (fun f => (H.obj r₀).map x ≫ f) hn.symm
    _ = (H.obj r₀).map (z ≫ w) ≫ (H.map (c ≫ d)).app l₂ := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hl, hr]
    _ = _ := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        NatTrans.comp_app]
      simp only [Category.assoc]
      rw [(H.map c).naturality_assoc, (H.map c).naturality_assoc]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 閉零両因子上の二段階sourceを既存の全導来sourceへ送る表示同型。 -/
def middleIteratedClosedSourceIso (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    ((middleIteratedDerivedSource A B D E T L F G hL).obj
      ((bimoduleToDerived A T L).obj Q)).obj ((bimoduleToDerived A B T).obj P) :=
  ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).mapIso
      ((middleLeftIteratedDerivedIso A B D E T F G).app P) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((middleRightIteratedDerivedIso A L D E T F G).app Q)).app
      ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).obj
        ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj
          ((bimoduleToDerived A B T).obj P)))

/-- 直接左右制限の合成同型による、閉零表示上のsource正規化。 -/
def middleIteratedClosedNormalizationIso
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).obj
          ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q)))).obj
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≅
    (middleClosedSourceFunctor A B T D L (F.comp G) hL).obj Q |>.obj P :=
  ((derivedBimoduleComposeFunctor A B D L hL).mapIso
      ((bimoduleToDerived A D L).mapIso
        ((BimoduleCategory.middleRightRestrictionCompIso A D L E T F G).app Q))).app
      ((bimoduleToDerived A B D).obj
        ((BimoduleCategory.middleLeftRestrictionFunctor A B E D F).obj
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))) ≪≫
    ((derivedBimoduleComposeFunctor A B D L hL).obj
      ((bimoduleToDerived A D L).obj
        ((BimoduleCategory.middleRightRestrictionFunctor A T D L (F.comp G)).obj Q))).mapIso
      ((bimoduleToDerived A B D).mapIso
        ((BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).app P))

/-- 全導来sourceの正規化は、直接制限の閉零表示における正規化と可換。 -/
lemma middleIteratedClosedSourceIso_normalize
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T) :
    (middleIteratedClosedSourceIso A B D E T L F G hL Q P).hom ≫
        ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app
          ((bimoduleToDerived A T L).obj Q)).app ((bimoduleToDerived A B T).obj P) =
      (middleIteratedClosedNormalizationIso A B D E T L F G hL Q P).hom ≫
        ((middleClosedSourceIdentification A B T D L (F.comp G) hL).hom.app Q).app P := by
  have hr := NatTrans.congr_app
    (middleRightIteratedDerivedIso_normalize A L D E T F G) Q
  have hl := NatTrans.congr_app
    (middleLeftIteratedDerivedIso_normalize A B D E T F G) P
  have h := bifunctor_square (derivedBimoduleComposeFunctor A B D L hL)
    ((middleRightIteratedDerivedIso A L D E T F G).hom.app Q)
    ((middleRightDerivedCompIso A L D E T F G).hom.app
      ((bimoduleToDerived A T L).obj Q))
    ((bimoduleToDerived A D L).map
      ((BimoduleCategory.middleRightRestrictionCompIso A D L E T F G).hom.app Q))
    ((middleRightRestrictionDerivedIso A T D (F.comp G) L).hom.app Q)
    ((middleLeftIteratedDerivedIso A B D E T F G).hom.app P)
    ((middleLeftDerivedCompIso A B D E T F G).hom.app ((bimoduleToDerived A B T).obj P))
    ((bimoduleToDerived A B D).map
      ((BimoduleCategory.middleLeftRestrictionCompIso A B D E T F G).hom.app P))
    ((middleLeftRestrictionDerivedIso A B T D (F.comp G)).hom.app P) hr hl
  simpa only [middleIteratedClosedSourceIso, middleIteratedClosedNormalizationIso,
    middleIteratedDerivedSourceIso, middleClosedSourceIdentification,
    Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, whiskeringLeft, Functor.comp_obj,
    Functor.comp_map, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
