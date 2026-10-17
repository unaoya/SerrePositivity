module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleAugmentedTransport

/-! # 二段階全導来比較を指定K-flatモデルと増大で計算する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 増大に準同型性を課さず、二段階比較を任意の右K-flatモデル上で計算する。 -/
lemma middleIteratedAugmentedComparison_fac
    (Q : RightKFlatBimoduleCategory A T L) (P : BimoduleCategory A B T)
    (R : RightKFlatBimoduleCategory A E L)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj) :
    middleIteratedAugmentedSourceMap A B D E T L F G hL Q.obj P R.obj q ≫
        ((middleIteratedDerivedComparison A B D E T L F G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P) =
      derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) R ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map q)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q := by
  let P₀ := (BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P
  let Q' := (derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj
    ((bimoduleToDerived A T L).obj Q.obj)
  let P' := (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj
    ((bimoduleToDerived A B T).obj P)
  let g := (bimoduleToDerived A E L).map q ≫
    (middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj
  let f := (middleLeftRestrictionDerivedIso A B T E G).hom.app P
  have he :
      ((derivedBimoduleComposeFunctor A B E L hL).map
          ((middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj)).app
          ((bimoduleToDerived A B E).obj P₀) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).obj Q').map f =
      (middleDerivedSourceFamilyIdentification A B T E L G hL Q).hom.app P := by
    have hn := ((derivedBimoduleComposeFunctor A B E L hL).map
      ((middleRightRestrictionDerivedIso A T E G L).hom.app Q.obj)).naturality f
    simpa only [middleDerivedSourceFamilyIdentification, middleClosedSourceIdentification,
      Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, whiskerLeft_app,
      whiskerRight_app, whiskeringLeft, Functor.comp_obj, Functor.comp_map] using hn.symm
  have h := derivedMiddleRestrictionNatTrans_transport_fac A B E D L F hL R P₀ Q' P' g f
  calc
    _ = (derivedMiddleRestrictionCanonicalComparison A B E D L F hL P₀ R ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map g).app
          ((bimoduleToDerived A B E).obj P₀) ≫
        ((derivedBimoduleComposeFunctor A B E L hL).obj Q').map f) ≫
      ((derivedMiddleRestrictionNatTrans A B T E L G hL).app
        ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P) := by
      simpa only [middleIteratedDerivedComparison_app,
        middleIteratedAugmentedSourceMap_transport, Category.assoc] using
        congrArg (fun k => k ≫ ((derivedMiddleRestrictionNatTrans A B T E L G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P)) h
    _ = _ := by
      dsimp only [g]
      rw [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
      simp only [Category.assoc]
      rw [← Category.assoc _ _
        (((derivedMiddleRestrictionNatTrans A B T E L G hL).app
          ((bimoduleToDerived A T L).obj Q.obj)).app ((bimoduleToDerived A B T).obj P)), he]
      rw [derivedMiddleRestrictionNatTrans_base_fac]

end SerrePositivity.DifferentialGraded.BimoduleTensor
