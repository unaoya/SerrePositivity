module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionAssociatorIndependence

/-! # 全導来結合同型と既存K-flat結合同型の比較図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z) (F : Type t)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F]

lemma derivedBimoduleComposePairResolutionIso_self (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposePairResolutionIso A B C E F hE hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      isoWhiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S)
          ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≪≫
        isoWhiskerLeft (derivedComposeWith A B C E S.obj S.property)
          (derivedBimoduleComposeKFlatIso A B E F hF T) := by
  unfold derivedBimoduleComposePairResolutionIso
  rw [derivedBimoduleComposeResolutionComputation_self,
    derivedBimoduleComposeResolutionComputation_self]

lemma derivedBimoduleComposeInnerResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeInnerResolutionIso A C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj := by
  have hi : bimoduleDerivedIso A C E (𝟙 S.obj)
      ((BimoduleCategory.quasiIso A C E).id_mem S.obj) = Iso.refl _ := by
    apply Iso.ext
    exact (bimoduleToDerived A C E).map_id _
  apply Iso.ext
  change (derivedBimoduleComposeResolutionComputation A C E F hF T.obj T (𝟙 T.obj)
      ((BimoduleCategory.quasiIso A E F).id_mem T.obj)).hom.app
        ((bimoduleToDerived A C E).obj S.obj) ≫
      (derivedComposeWith A C E F T.obj T.property).map
        (bimoduleDerivedIso A C E (𝟙 S.obj)
          ((BimoduleCategory.quasiIso A C E).id_mem S.obj)).inv = _
  rw [hi, Iso.refl_inv, derivedBimoduleComposeResolutionComputation_self,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

lemma derivedBimoduleComposeNestedResolutionIso_self (hF : localHomKFlat A F)
    (S : RightKFlatBimoduleCategory A C E) (T : RightKFlatBimoduleCategory A E F) :
    derivedBimoduleComposeNestedResolutionIso A B C E F hF S.obj T.obj S T (𝟙 S.obj) (𝟙 T.obj)
        ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
        ((BimoduleCategory.quasiIso A E F).id_mem T.obj) =
      (derivedBimoduleComposeFunctor A B C F hF).mapIso
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj) ≪≫
        derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T) := by
  unfold derivedBimoduleComposeNestedResolutionIso
  rw [derivedBimoduleComposeInnerResolutionIso_self]

lemma derivedBimoduleAssociatorIso_kFlat_fac (hE : localHomKFlat A E)
    (hF : localHomKFlat A F) (S : RightKFlatBimoduleCategory A C E)
    (T : RightKFlatBimoduleCategory A E F) :
    (((derivedBimoduleAssociatorIso A B C E F hE hF).app
        ((bimoduleToDerived A E F).obj T.obj)).app ((bimoduleToDerived A C E).obj S.obj)).hom ≫
      ((derivedBimoduleComposeFunctor A B C F hF).map
          (derivedBimoduleComposeKFlatValueIso A C E F hF T S.obj).hom ≫
        (derivedBimoduleComposeKFlatIso A B C F hF (rightKFlatCompose A C E F S T)).hom) =
    (whiskerRight (derivedBimoduleComposeKFlatIso A B C E hE S).hom
        ((derivedBimoduleComposeFunctor A B E F hF).obj ((bimoduleToDerived A E F).obj T.obj)) ≫
      whiskerLeft (derivedComposeWith A B C E S.obj S.property)
        (derivedBimoduleComposeKFlatIso A B E F hF T).hom) ≫
      (rightKFlatDerivedAssociator A B C E F S T).hom := by
  have h := derivedBimoduleAssociatorIso_resolution_fac A B C E F hE hF S.obj T.obj S T
    (𝟙 S.obj) (𝟙 T.obj) ((BimoduleCategory.quasiIso A C E).id_mem S.obj)
    ((BimoduleCategory.quasiIso A E F).id_mem T.obj)
  rw [derivedBimoduleComposePairResolutionIso_self,
    derivedBimoduleComposeNestedResolutionIso_self] at h
  exact h

end SerrePositivity.DifferentialGraded.BimoduleTensor
