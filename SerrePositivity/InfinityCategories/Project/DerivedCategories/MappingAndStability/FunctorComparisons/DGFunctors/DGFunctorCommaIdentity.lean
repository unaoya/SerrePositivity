module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedIdentityWhiskering
/-!
概要：commaの実 Hom 複体に、入力と出力の恒等射を持ち上げる実単位を構成する。
方針：閉じた augmentation の前後合成が同じ射となることから、比較 cochain を零とする。
規約：単位律の検証は別工程。使われ方：comma dg 圏の eId。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 同じ入力と比較対象の実恒等射の比較差は零。 -/
lemma dgFunctorCommaIdentity_difference :
    biprod.lift (eId (Complex R) X.source)
      (eId (Complex R) X.replacement) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X X = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_lift_difference
    (eId (Complex R) X.source) (eId (Complex R) X.replacement)
    (F.map X.source X.source ≫ eHomWhiskerRight (Complex R) X.augmentation
      (ForgetEnrichment.of (Complex R) (F.obj X.source)))
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement) X.augmentation)
  change biprod.lift _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X X = 0
  trans eId (Complex R) X.source ≫ F.map X.source X.source ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) (F.obj X.source)) -
    eId (Complex R) X.replacement ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement) X.augmentation
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference, Category.assoc] using! h
  · rw [← Category.assoc, F.map_id]
    have hp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_precompose (Complex R)
      (ForgetEnrichment (Complex R) E) X.augmentation
    have hq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R)
      (ForgetEnrichment (Complex R) E) X.augmentation
    exact sub_eq_zero.mpr (hp.trans hq.symm)
/-- 零の比較 cochain は、同じ実二恒等射の持ち上げ条件を満たす。 -/
lemma dgFunctorCommaIdentity_boundary :
    δ (-1) 0 (0 : Cochain (𝟙_ (Complex R))
      (homObject R E X.replacement (F.obj X.source)) (-1)) +
      Cochain.ofHom (biprod.lift (eId (Complex R) X.source)
        (eId (Complex R) X.replacement) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X X) = 0 := by
  rw [dgFunctorCommaIdentity_difference]
  simp
/-- 実入力と実比較対象の恒等射を、同じ比較 cochain 零とともに持ち上げる。 -/
def dgFunctorCommaIdentity :
    𝟙_ (Complex R) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X X :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift R C E F X X _ (eId (Complex R) X.source)
    (eId (Complex R) X.replacement) 0
    (dgFunctorCommaIdentity_boundary R C E F X)
/-- 実単位の入力射影は、元の同じ豊穣恒等射。 -/
lemma dgFunctorCommaIdentity_source :
    dgFunctorCommaIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSourceHomMap R C E F X X = eId (Complex R) X.source :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_source R C E F X X _ _ _ _ _
/-- 実単位の出力射影は、分解の同じ豊穣恒等射。 -/
lemma dgFunctorCommaIdentity_replacement :
    dgFunctorCommaIdentity R C E F X ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaReplacementHomMap R C E F X X =
        eId (Complex R) X.replacement :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomLift_replacement R C E F X X _ _ _ _ _
/-- 実単位の比較 cochain は厳密に零。 -/
lemma dgFunctorCommaIdentity_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F X X _
      (dgFunctorCommaIdentity R C E F X) = 0 := by
  apply Cochain.ext
  intro p q hpq
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v]
  exact mappingCocone.lift_f_snd_v
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaDifference R C E F X X)
    (biprod.lift (eId (Complex R) X.source) (eId (Complex R) X.replacement)) 0
    (dgFunctorCommaIdentity_boundary R C E F X) p q hpq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
