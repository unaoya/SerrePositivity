module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ParameterBiprodMapDifference
/-!
概要：入力 dg 関手の前合成に沿い、同じ出力分解対象と比較差を移す。
方針：同じ全 Hom・実二射影・比較 cochain の等式を保持して構成する。
規約：元の出力の射影性と入力の小ささは不要。使われ方：二変数 Hom の固定入力制限の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
/-- 同じ半自由 replacement と augmentation を保つ実分解対象。 -/
def dgModuleResolutionPrecompObject
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F where
  source := H.obj X.source
  replacement := X.replacement
  augmentation := X.augmentation
  surjective := X.surjective
  quasiIso := X.quasiIso
/-- 同じ比較差は、入力 Hom だけへの H.map と厳密に可換。 -/
lemma dgModuleResolutionPrecomp_difference
    (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R A E (H.comp F) X Y =
      biprod.map (H.map X.source Y.source) (𝟙 _) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference R C E F
          (dgModuleResolutionPrecompObject R A C E H F X)
          (dgModuleResolutionPrecompObject R A C E H F Y) := by
  let a := H.map X.source Y.source
  let b := 𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val Y.replacement.val)
  let p := F.map (H.obj X.source) (H.obj Y.source) ≫
    eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R) X.augmentation
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (F.obj (H.obj Y.source)))
  let q := eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val) Y.augmentation
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.parameterBiprod_map_difference a b p q
  simpa only [a, b, p, q, dgModuleResolutionPrecompObject,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionDifference, EnrichedFunctor.comp_map,
    Category.id_comp, Category.assoc] using! h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
