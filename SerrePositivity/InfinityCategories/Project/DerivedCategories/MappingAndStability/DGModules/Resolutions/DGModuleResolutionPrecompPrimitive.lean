module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Resolutions.DGModuleResolutionPrecompCompositionMaps
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.ComplexTensorCochainSquare
/-!
概要：前合成比較は、同じ二つの合成比較 cochain とその和を保存する。
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
/-- 同じ第一合成比較 cochain を全次数で保つ。 -/
lemma dgModuleResolutionPrecomp_firstPrimitive
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R A E (H.comp F) X Y Z := by
  let X' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X
  let Y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y
  let Z' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z
  let b := 𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val ((H.comp F).obj Y.source))
  let c := 𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val ((H.comp F).obj Z.source))
  have hp : (Cochain.ofHom f).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X' Y')
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y).comp
      (Cochain.ofHom b) (add_zero (-1)) := by
    simpa only [b, Cochain.comp_id] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R A C E H F X Y
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorRight_cochain_square (-1) f g b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X' Y') hp
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cochain_postcompose_square (-1) (f ⊗ₘ g) (b ⊗ₘ g) c
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R A E (H.comp F) X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F X' Y' Z') _ _ ht
    (by simpa only [c, Category.comp_id] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecomp_firstCompositionMap R A C E H F X Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive, c, Cochain.comp_id] using! h
/-- 同じ第二合成比較 cochain を全次数で保つ。 -/
lemma dgModuleResolutionPrecomp_secondPrimitive
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R A E (H.comp F) X Y Z := by
  let X' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X
  let Y' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y
  let Z' := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z
  let f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y
  let g := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z
  let b := 𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E Y.replacement.val ((H.comp F).obj Z.source))
  let c := 𝟙 (_root_.SerrePositivity.DifferentialGraded.moduleHom R E X.replacement.val ((H.comp F).obj Z.source))
  have hp : (Cochain.ofHom g).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F Y' Z')
      (zero_add (-1)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp F) Y Z).comp
      (Cochain.ofHom b) (add_zero (-1)) := by
    simpa only [b, Cochain.comp_id] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom_comparison R A C E H F Y Z
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorLeft_cochain_square (-1) f g b
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R A E (H.comp F) Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F Y' Z') hp
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cochain_postcompose_square (-1) (f ⊗ₘ g) (f ⊗ₘ b) c
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R A E (H.comp F) X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F X' Y' Z') _ _ ht
    (by simpa only [c, Category.comp_id] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecomp_secondCompositionMap R A C E H F X Y Z)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive, c, Cochain.comp_id] using! h
/-- 同じ二項の和による合成比較 cochain を保つ。 -/
lemma dgModuleResolutionPrecomp_compositePrimitive
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive R C E F
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive R A E (H.comp F) X Y Z := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleResolutionPrecomp_firstPrimitive, dgModuleResolutionPrecomp_secondPrimitive]
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
