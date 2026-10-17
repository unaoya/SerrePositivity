module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleQuasiIso

/-! # dg準同値に沿う中間圏比較の全導来自然同型 -/
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
  (hF : QuasiEquivalence F) (hE : localHomKFlat A E)
include hF

lemma derivedMiddleRestrictionComparison_isIso (P : BimoduleCategory A B C)
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    IsIso (derivedMiddleRestrictionComparison A B C D E F hE P Q R q hq) := by
  have hm := bimoduleToDerived_inverts A B E _
    (middleRestrictionResolvedMap_quasiIso A B C D E F hF P Q R q hq)
  let := hm
  unfold derivedMiddleRestrictionComparison
  infer_instance

lemma derivedMiddleRestrictionComparisonLocalized_isIso
    (Q : RightKFlatBimoduleCategory A C E) (R : RightKFlatBimoduleCategory A D E)
    (q : R.obj ⟶ (BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj)
    (hq : BimoduleCategory.quasiIso A D E q) :
    IsIso (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  obtain ⟨P, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (bimoduleToDerived A B C) X
  apply (NatTrans.isIso_app_iff_of_iso
    (derivedMiddleRestrictionComparisonLocalized A B C D E F hE Q R q hq) e).mp
  rw [derivedMiddleRestrictionComparisonLocalized_app]
  have hi := derivedMiddleRestrictionComparison_isIso A B C D E F hF hE P Q R q hq
  let := hi
  infer_instance

lemma middleDerivedKFlatComparison_isIso :
    IsIso (middleDerivedKFlatComparison A B C D E F hE) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Q
  exact derivedMiddleRestrictionComparisonLocalized_isIso A B C D E F hF hE Q
    (rightKFlatResolutionObj A D E hE
      ((BimoduleCategory.middleRightRestrictionFunctor A C D E F).obj Q.obj))
    (bimoduleCanonicalSemifreeResolution A D E _).π
    (bimoduleCanonicalSemifreeResolution A D E _).quasiIso

lemma middleRightKFlatLocalizedComparison_isIso :
    IsIso (middleRightKFlatLocalizedComparison A B C D E F hE) := by
  have hi := middleDerivedKFlatComparison_isIso A B C D E F hF hE
  let := hi
  exact (Localization.liftNatIso (rightKFlatToDerived A C E) (rightKFlatQuasiIso A C E)
    (middleDerivedSourceKFlatFunctor A B C D E F hE)
    (middleDerivedTargetKFlatFunctor A B C E hE)
    (middleRightKFlatLocalizedSource A B C D E F hE)
    (rightKFlatDerivedInclusion A C E ⋙ derivedBimoduleComposeFunctor A B C E hE)
    (asIso (middleDerivedKFlatComparison A B C D E F hE))).isIso_hom

lemma middleFullDerivedComparison_isIso :
    IsIso (middleFullDerivedComparison A B C D E F hE) := by
  have hi := middleRightKFlatLocalizedComparison_isIso A B C D E F hF hE
  let := hi
  unfold middleFullDerivedComparison
  infer_instance

lemma derivedMiddleRestrictionNatTrans_isIso :
    IsIso (derivedMiddleRestrictionNatTrans A B C D E F hE) := by
  have hi := middleFullDerivedComparison_isIso A B C D E F hF hE
  let := hi
  unfold derivedMiddleRestrictionNatTrans
  infer_instance

/-- 準同値に沿う中間圏の変更は、両変数の全導来射に自然な合成比較同型を与える。 -/
def derivedMiddleRestrictionIso :
    middleRestrictionDerivedSource A B C D E F hE ≅
      derivedBimoduleComposeFunctor A B C E hE := by
  have hi := derivedMiddleRestrictionNatTrans_isIso A B C D E F hF hE
  let := hi
  exact asIso (derivedMiddleRestrictionNatTrans A B C D E F hE)

lemma derivedMiddleRestrictionIso_hom :
    (derivedMiddleRestrictionIso A B C D E F hF hE).hom =
      derivedMiddleRestrictionNatTrans A B C D E F hE := rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
