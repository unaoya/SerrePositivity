module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.FullFunctor

/-!
概要：閉包代表へ共役した関手と、元の実関手との比較を自然同型へ束ねる。
方針：保持した同じ実同型の全 Hom 自然性を使い、成分を変更しない。
規約：元の実延長と代表評価の比較。入力関手族の高次作用は主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (F : DGFunctor R (RightModule R C) (RightModule R D))
  (S : Set (ModuleCategory R C)) (T : Set (ModuleCategory R D))
  (I : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage R C D F S T)

/-- 保持した実比較同型は、元の全 Hom 鎖写像に対して自然である。 -/
lemma DGModuleStrictImage.comparison_naturality (M N : {M // S M}) :
    F.map (ForgetEnrichment.to (Complex R) M.val)
        (ForgetEnrichment.to (Complex R) N.val) ≫
      eHomWhiskerLeft (Complex R) (F.onClosed.obj M.val) (I.iso N).hom =
    (I.functor R C D F S T).map M N ≫
      eHomWhiskerRight (Complex R) (I.iso M).hom (I.obj N).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor_map, Category.assoc]
  rw [enrichedClosedIsoConjugation_naturality]

/-- 元の実関手と、固定閉包代表へ移した関手の評価の閉零自然同型。 -/
def DGModuleStrictImage.comparisonIso :
    (((dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
      (dgConeModuleForget R C)).comp F).onClosed ≅
    (((I.functor R C D F S T).comp
      (dgFullSubcategoryInclusion R (ModuleCategory R D) T)).comp
      (dgConeModuleForget R D)).onClosed := by
  refine dgFunctorClosedComparisonIso R _ _ I.iso (fun M N => ?_)
  simpa only [DGFunctor.comp, EnrichedFunctor.comp, dgFullSubcategoryInclusion,
    dgConeModuleForget, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.functor, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.DGModuleStrictImage.evaluated,
    Category.id_comp, Category.comp_id] using
    dgFunctorClosedConjugate_naturality R
      (((dgFullSubcategoryInclusion R (ModuleCategory R C) S).comp
        (dgConeModuleForget R C)).comp F)
      (fun M => ForgetEnrichment.to (Complex R) (I.obj M).val) I.iso M N

/-- 自然同型の成分は、元の指定実比較の hom そのもの。 -/
lemma DGModuleStrictImage.comparisonIso_hom_app
    (M : ClosedCategory R {M // S M}) :
    (I.comparisonIso R C D F S T).hom.app M =
      (I.iso (ForgetEnrichment.to (Complex R) M)).hom := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
