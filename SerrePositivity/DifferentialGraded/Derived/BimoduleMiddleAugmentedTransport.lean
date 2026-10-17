module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleAugmentedSource
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleTransportComputation

/-! # 指定増大による二段階sourceと移送計算の接続 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor

private lemma bifunctor_transport
    {C D E : Type*} [Category* C] [Category* D] [Category* E] (H : C ⥤ D ⥤ E)
    {r₀ r₁ r₂ r₃ r₄ : C} {l₀ l₁ l₂ : D}
    (c : r₀ ⟶ r₁) (a : r₀ ⟶ r₂) (b : r₁ ⟶ r₃) (d : r₂ ⟶ r₃) (e : r₃ ⟶ r₄)
    (x : l₀ ⟶ l₁) (y : l₁ ⟶ l₂) (hr : c ≫ b = a ≫ d) :
    (H.map c).app l₀ ≫ (H.obj r₁).map x ≫ (H.obj r₁).map y ≫
        (H.map b).app l₂ ≫ (H.map e).app l₂ =
      (H.obj r₀).map x ≫ (H.map a).app l₁ ≫ (H.map d).app l₁ ≫
        (H.map e).app l₁ ≫ (H.obj r₄).map y := by
  have hrt : c ≫ b ≫ e = a ≫ d ≫ e := by
    simpa only [Category.assoc] using congrArg (fun f => f ≫ e) hr
  calc
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (c ≫ b ≫ e)).app l₂ := by
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
      rw [← (H.map c).naturality_assoc, ← (H.map c).naturality_assoc]
    _ = (H.obj r₀).map x ≫ (H.obj r₀).map y ≫ (H.map (a ≫ d ≫ e)).app l₂ := by rw [hrt]
    _ = _ := by
      rw [(H.map (a ≫ d ≫ e)).naturality y]
      simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]

variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 指定増大によるsource射は、前段比較のsourceを両変数で移送する射に一致する。 -/
lemma middleIteratedAugmentedSourceMap_transport
    (Q : BimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : RightKFlatBimoduleCategory A E L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q P R.obj q =
      (middleDerivedSourceFamilyIdentification A B E D L F hL R).hom.app
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) ≫
        ((middleRestrictionDerivedSource A B E D L F hL).map
          ((bimoduleToDerived A E L).map q ≫
            (middleRightRestrictionDerivedIso A T E G L).hom.app Q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        ((middleRestrictionDerivedSource A B E D L F hL).obj
          ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj
            ((bimoduleToDerived A T L).obj Q))).map
          ((middleLeftRestrictionDerivedIso A B T E G).hom.app P) := by
  have hr := (middleRightRestrictionDerivedIso A E D F L).hom.naturality q
  simp only [Functor.comp_map] at hr
  have h := bifunctor_transport (derivedBimoduleComposeFunctor A B D L hL)
    ((bimoduleToDerived A D L).map
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map q))
    ((middleRightRestrictionDerivedIso A E D F L).hom.app R.obj)
    ((middleRightRestrictionDerivedIso A E D F L).hom.app
      ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q))
    ((derivedBimoduleRestriction A D L E L F (DGFunctor.id L)).map
      ((bimoduleToDerived A E L).map q))
    ((derivedBimoduleRestriction A D L E L F (DGFunctor.id L)).map
      ((middleRightRestrictionDerivedIso A T E G L).hom.app Q))
    ((middleLeftRestrictionDerivedIso A B E D F).hom.app
      ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P))
    ((derivedBimoduleRestriction A B D B E (DGFunctor.id B) F).map
      ((middleLeftRestrictionDerivedIso A B T E G).hom.app P)) hr
  simpa only [middleIteratedAugmentedSourceMap, middleIteratedClosedSourceIso,
    middleLeftIteratedDerivedIso, middleRightIteratedDerivedIso,
    middleDerivedSourceFamilyIdentification, middleClosedSourceIdentification,
    middleRestrictionDerivedSource, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, whiskeringLeft, Functor.comp_map, Functor.comp_obj,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

end SerrePositivity.DifferentialGraded.BimoduleTensor
