module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionPrecompInfinity
/-!
概要：入力前合成に沿う実分解 dg 関手は、同じ全 Hom と比較 cochain 上で合成を保つ。
方針：二つの射影と比較 cochain の外延性から、指定 dg 関手の厳密等式を得る。
規約：出力分解対象と augmentation を保持する。使われ方：実出力分解の前合成則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (A B C : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R A] [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 二段の入力前合成は、同じ実分解 dg 関手の合成に厳密に一致する。 -/
lemma dgModuleResolutionPrecompFunctor_comp
    (H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R A B) (J : _root_.SerrePositivity.DifferentialGraded.DGFunctor R B C) (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E (H.comp J) F =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A B E H (J.comp F)).comp
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R B C E J F) := by
  apply EnrichedFunctor.ext (_root_.SerrePositivity.DifferentialGraded.Complex R)
    (F := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A C E (H.comp J) F)
    (G := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R A B E H (J.comp F)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor R B C E J F)) (fun _ => rfl)
  intro X Y
  simp only [EnrichedFunctor.comp_map, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompFunctor,
    eqToHom_refl, Category.comp_id]
  let X' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A B E H (J.comp F) X
  let Y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A B E H (J.comp F) Y
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A B E H (J.comp F) X Y
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R B C E J F X' Y'
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHom_ext R C E F
  · have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R A C E (H.comp J) F X Y
    have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R B C E J F X' Y'
    have h3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_source R A B E H (J.comp F) X Y
    have h23 := congrArg (fun t => f ≫ t) h2
    simp only [← Category.assoc] at h23
    rw [h3] at h23
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceHomMap R A E ((H.comp J).comp F) X Y ≫
          H.map X.source Y.source ≫ J.map (H.obj X.source) (H.obj Y.source) := by
        simpa only [EnrichedFunctor.comp_map, Category.assoc] using! h1
      _ = _ := by simpa only [Category.assoc] using! h23.symm
  · have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R A C E (H.comp J) F X Y
    have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R B C E J F X' Y'
    have h3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R A B E H (J.comp F) X Y
    have h23 := congrArg (fun t => f ≫ t) h2
    rw [h3] at h23
    exact h1.trans (by simpa only [Category.assoc] using! h23.symm)
  · have h1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R A C E (H.comp J) F X Y
    have h2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison_precompose R C E F
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R B C E J F X')
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R B C E J F Y') f g
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison] at h2
    have h3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R A B E H (J.comp F) X Y
    have h23 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComparison R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R B C E J F X')
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R B C E J F Y') _ (f ≫ g) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp (J.comp F)) X Y :=
      h2.trans h3
    exact h1.trans (by simpa only using! h23.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
