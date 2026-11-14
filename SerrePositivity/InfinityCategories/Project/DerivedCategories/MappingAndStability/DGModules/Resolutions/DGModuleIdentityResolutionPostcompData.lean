module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleFunctorResolutionCompositionMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionChangeData
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.EnrichedClosedWhiskering
/-!
概要：同じ replacement を保ち入力を準同型で後合成した実分解対象と比較差零を構成する。
方針：実二射影と mapping cocone の持ち上げを使う。
規約：分解変更比較の同定は別工程。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
variable (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
  (DGFunctor.id (A := R) (RightModule R E)))
  (M : RightModule R E)
  (a : ForgetEnrichment.of (Complex R) X.source ⟶ ForgetEnrichment.of (Complex R) M)
  (hs : moduleDegreewiseSurjective R E a) (hq : moduleQuasiIso R E a)
def dgModuleIdentityResolutionPostcompObject :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (RightModule R E) E
      (DGFunctor.id (A := R) (RightModule R E)) where
  source := M
  replacement := X.replacement
  augmentation := X.augmentation ≫ a
  surjective d n := by
    apply (moduleSurjectiveAt_iff_epi R E d n _).2
    have := (moduleSurjectiveAt_iff_epi R E d n _).1 (X.surjective d n)
    have := (moduleSurjectiveAt_iff_epi R E d n _).1 (hs d n)
    simp only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f]
    infer_instance
  quasiIso := (moduleQuasiIso R E).comp_mem _ _ X.quasiIso hq
lemma dgModuleIdentityResolutionPostcomp_difference :
    biprod.lift (ForgetEnrichment.homTo (Complex R) a)
      (eId (Complex R) X.replacement.val) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R (RightModule R E) E
          (DGFunctor.id (A := R) (RightModule R E)) X
          (dgModuleIdentityResolutionPostcompObject R E X M a hs hq) = 0 := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_lift_difference (ForgetEnrichment.homTo (Complex R) a)
    (eId (Complex R) X.replacement.val)
    (eHomWhiskerRight (Complex R) X.augmentation (ForgetEnrichment.of (Complex R) M))
    (eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) (X.augmentation ≫ a))
  trans ForgetEnrichment.homTo (Complex R) a ≫
      eHomWhiskerRight (Complex R) X.augmentation
        (ForgetEnrichment.of (Complex R) M) -
    eId (Complex R) X.replacement.val ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) X.replacement.val) (X.augmentation ≫ a)
  · simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference, EnrichedFunctor.id_map,
      Category.comp_id, Category.assoc] using! hh
  · have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedClosed_precompose (Complex R)
      (ForgetEnrichment (Complex R) (RightModule R E)) X.augmentation a
    have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.enrichedIdentity_postcompose (Complex R)
      (ForgetEnrichment (Complex R) (RightModule R E)) (X.augmentation ≫ a)
    exact sub_eq_zero.mpr (h₁.trans h₂.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
