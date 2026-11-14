module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedIdentityWhiskering
/-!
概要：出力分解の実 Hom 複体に、入力と出力の恒等射を持ち上げる実単位を構成する。
方針：閉じた augmentation の前後合成が同じ射となることから、比較 cochain を零とする。
規約：単位律の検証は別工程。使われ方：分解 dg 圏の eId。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 同じ入力と半自由出力の実恒等射の比較差は零。 -/
lemma dgModuleFunctorResolutionIdentity_difference :
    biprod.lift (eId (Complex R) X.source)
      (eId (Complex R) X.replacement.val) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X X = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_lift_difference
    (eId (Complex R) X.source) (eId (Complex R) X.replacement.val)
    (F.map X.source X.source ≫ eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj X.source)))
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) X.augmentation)
  change biprod.lift _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X X = 0
  trans eId (Complex R) X.source ≫ F.map X.source X.source ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj X.source)) -
    eId (Complex R) X.replacement.val ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) X.augmentation
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference, Category.assoc] using! h
  · rw [← Category.assoc, F.map_id]
    have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_precompose (Complex R)
      (ForgetEnrichment (Complex R) (RightModule R E)) X.augmentation
    have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R)
      (ForgetEnrichment (Complex R) (RightModule R E)) X.augmentation
    exact sub_eq_zero.mpr (hp.trans hq.symm)
/-- 零の比較 cochain は、同じ実二恒等射の持ち上げ条件を満たす。 -/
lemma dgModuleFunctorResolutionIdentity_boundary :
    δ (-1) 0 (0 : Cochain (𝟙_ (Complex R))
      (moduleHom R E X.replacement.val (F.obj X.source)) (-1)) +
      Cochain.ofHom (biprod.lift (eId (Complex R) X.source)
        (eId (Complex R) X.replacement.val) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X X) = 0 := by
  rw [dgModuleFunctorResolutionIdentity_difference]
  simp
/-- 実入力と実半自由出力の恒等射を、同じ比較 cochain 零とともに持ち上げる。 -/
def dgModuleFunctorResolutionIdentity :
    𝟙_ (Complex R) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomLift R C E F X X _ (eId (Complex R) X.source)
    (eId (Complex R) X.replacement.val) 0
    (dgModuleFunctorResolutionIdentity_boundary R C E F X)
/-- 実単位の入力射影は、元の同じ豊穣恒等射。 -/
lemma dgModuleFunctorResolutionIdentity_source :
    dgModuleFunctorResolutionIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R C E F X X = eId (Complex R) X.source :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomLift_source R C E F X X _ _ _ _ _
/-- 実単位の出力射影は、分解の同じ豊穣恒等射。 -/
lemma dgModuleFunctorResolutionIdentity_replacement :
    dgModuleFunctorResolutionIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F X X =
        eId (Complex R) X.replacement.val :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomLift_replacement R C E F X X _ _ _ _ _
/-- 実単位の比較 cochain は厳密に零。 -/
lemma dgModuleFunctorResolutionIdentity_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R C E F X X _
      (dgModuleFunctorResolutionIdentity R C E F X) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F X X)
    (biprod.lift (eId (Complex R) X.source) (eId (Complex R) X.replacement.val)) 0
    (dgModuleFunctorResolutionIdentity_boundary R C E F X) p q hpq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
