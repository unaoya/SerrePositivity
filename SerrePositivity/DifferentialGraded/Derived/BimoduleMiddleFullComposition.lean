module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleIteratedComputation
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleEquivalence

/-! # 中間dg圏制限の合成則を両変数の全導来圏へ降ろす -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (D : Type w) [DGCategory A D] [Small.{u} D]
  (E : Type z) [DGCategory A E] [Small.{u} E]
  (T : Type t) [DGCategory A T] [Small.{u} T]
  (L : Type s) [DGCategory A L] [Small.{u} L]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (hL : localHomKFlat A L)

/-- 実際の二段階全導来比較は、合成dg関手の比較と独立に構成したsource正規化の合成に一致。 -/
lemma derivedMiddleRestrictionNatTrans_functor_comp :
    (middleIteratedDerivedSourceIso A B D E T L F G hL).hom ≫
        derivedMiddleRestrictionNatTrans A B T D L (F.comp G) hL =
      middleIteratedDerivedComparison A B D E T L F G hL := by
  apply middleDerivedFamily_ext A B T L hL
  intro Q P
  let R := bimoduleCanonicalSemifreeResolution A E L
    ((BimoduleCategory.middleRightRestrictionFunctor A T E L G).obj Q.obj)
  let Rf := R.toRightKFlat A E L hL
  let a := middleIteratedAugmentedSourceMap A B D E T L F G hL Q.obj P R.obj R.π
  have hq : BimoduleCategory.quasiIso A D L
      ((BimoduleCategory.middleRightRestrictionFunctor A E D L F).map R.π) := by
    intro d l
    change QuasiIso ((BimoduleCategory.valueEvaluation A D L d l).map
      (BimoduleCategory.middleRightRestrictionMap A E D L F R.π))
    rw [BimoduleCategory.middleRightRestrictionMap_value_eval]
    exact R.quasiIso (F.obj d) l
  have hi := bimoduleToDerived_inverts A D L _ hq
  have ha : IsIso a := by
    dsimp only [a, middleIteratedAugmentedSourceMap]
    infer_instance
  apply (cancel_epi a).mp
  simp only [NatTrans.comp_app]
  calc
    _ = (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π
        R.quasiIso).hom ≫
        derivedMiddleRestrictionCanonicalComparison A B T D L (F.comp G) hL P Q := by
      dsimp only [a]
      rw [← Category.assoc, middleIteratedAugmentedSourceMap_normalize, Category.assoc]
      exact congrArg (fun f =>
        (derivedMiddleCompositeSourceIso A B D L hL E T F G P Q.obj R.obj R.π
          R.quasiIso).hom ≫ f)
        (derivedMiddleRestrictionNatTrans_base_fac A B T D L (F.comp G) hL Q P)
    _ = derivedMiddleRestrictionCanonicalComparison A B E D L F hL
          ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P) Rf ≫
        ((derivedBimoduleComposeFunctor A B E L hL).map ((bimoduleToDerived A E L).map R.π)).app
          ((bimoduleToDerived A B E).obj
            ((BimoduleCategory.middleLeftRestrictionFunctor A B T E G).obj P)) ≫
        derivedMiddleRestrictionCanonicalComparison A B T E L G hL P Q :=
      derivedMiddleRestrictionCanonicalComparison_functor_comp A B D E T L F G hL P Q
    _ = _ := (middleIteratedAugmentedComparison_fac A B D E T L F G hL Q P Rf R.π).symm

/-- 合成則の成分式は両変数とも任意の導来対象に適用できる。 -/
lemma derivedMiddleRestrictionNatTrans_functor_comp_app
    (Q : DerivedBimoduleCategory A T L) (P : DerivedBimoduleCategory A B T) :
    ((middleIteratedDerivedSourceIso A B D E T L F G hL).hom.app Q).app P ≫
        ((derivedMiddleRestrictionNatTrans A B T D L (F.comp G) hL).app Q).app P =
      ((derivedMiddleRestrictionNatTrans A B E D L F hL).app
          ((derivedBimoduleRestriction A E L T L G (DGFunctor.id L)).obj Q)).app
          ((derivedBimoduleRestriction A B E B T (DGFunctor.id B) G).obj P) ≫
        ((derivedMiddleRestrictionNatTrans A B T E L G hL).app Q).app P := by
  simpa only [NatTrans.comp_app, middleIteratedDerivedComparison_app] using
    NatTrans.congr_app (NatTrans.congr_app
      (derivedMiddleRestrictionNatTrans_functor_comp A B D E T L F G hL) Q) P

/-- 二つの準同値に対する、既存の比較自然同型を実際に二段階で適用する同型。 -/
def middleIteratedDerivedIso (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    middleIteratedDerivedSource A B D E T L F G hL ≅
      derivedBimoduleComposeFunctor A B T L hL :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (derivedBimoduleRestriction A E L T L G (DGFunctor.id L))
        (derivedMiddleRestrictionIso A B E D L F hF hL))
      ((Functor.whiskeringLeft _ _ _).obj
        (derivedBimoduleRestriction A B E B T (DGFunctor.id B) G)) ≪≫
    derivedMiddleRestrictionIso A B T E L G hG hL

/-- 準同値の場合の自然同型そのものの推移整合性。 -/
lemma derivedMiddleRestrictionIso_functor_comp
    (hF : QuasiEquivalence F) (hG : QuasiEquivalence G) :
    middleIteratedDerivedSourceIso A B D E T L F G hL ≪≫
        derivedMiddleRestrictionIso A B T D L (F.comp G)
          (quasiEquivalence_comp F G hF hG) hL =
      middleIteratedDerivedIso A B D E T L F G hL hF hG := by
  apply Iso.ext
  simpa only [Iso.trans_hom, middleIteratedDerivedIso,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    derivedMiddleRestrictionIso_hom, middleIteratedDerivedComparison] using
    derivedMiddleRestrictionNatTrans_functor_comp A B D E T L F G hL

end SerrePositivity.DifferentialGraded.BimoduleTensor
