module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolutionPrecompProjection
/-!
概要：前合成比較は、同じ二つの実合成作用を保存する。
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
/-- 同じ全 Hom 上の第一合成作用を保つ。 -/
lemma dgModuleResolutionPrecomp_firstCompositionMap
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val ((H.comp F).obj Y.source)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R A E (H.comp F) X Y Z := by
  let K := _root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val ((H.comp F).obj Y.source)
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionImageHomMap R C E F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z)
  let c := eComp (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val ((H.comp F).obj Y.source)
    ((H.comp F).obj Z.source)
  change (𝟙 K ⊗ₘ f) ≫ (𝟙 K ⊗ₘ i) ≫ c = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [show f ≫ i = _ from _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_image R A C E H F Y Z]
  rfl
/-- 同じ全 Hom 上の第二合成作用を保つ。 -/
lemma dgModuleResolutionPrecomp_secondCompositionMap
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E Y.replacement.val ((H.comp F).obj Z.source))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R A E (H.comp F) X Y Z := by
  let K := _root_.SerrePositivity.DifferentialGraded.moduleHom R E Y.replacement.val ((H.comp F).obj Z.source)
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y
  let i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionReplacementHomMap R C E F
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
  let c := eComp (_root_.SerrePositivity.DifferentialGraded.Complex R) X.replacement.val Y.replacement.val ((H.comp F).obj Z.source)
  change (f ⊗ₘ 𝟙 K) ≫ (i ⊗ₘ 𝟙 K) ≫ c = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [show f ≫ i = _ from _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_replacement R A C E H F X Y]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
