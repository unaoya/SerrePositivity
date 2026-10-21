module
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolutionPrecompCompositionMaps
public import SerrePositivity.InfinityCategories.Derived.ComplexTensorCochainSquare
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve MonoidalCategory
open CochainComplex HomComplex SSet
variable (R : Type u) [CommRing R] (A C : Type v) [DGCategory R A] [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E]
  (H : DGFunctor R A C) (F : DGFunctor R C (RightModule R E))
/-- 同じ第一合成比較 cochain を全次数で保つ。 -/
lemma dgModuleResolutionPrecomp_firstPrimitive
    (X Y Z : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y)
        (dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    dgModuleFunctorResolutionFirstCompositePrimitive R A E (H.comp F) X Y Z := by
  let X' := dgModuleResolutionPrecompObject R A C E H F X
  let Y' := dgModuleResolutionPrecompObject R A C E H F Y
  let Z' := dgModuleResolutionPrecompObject R A C E H F Z
  let f := dgModuleResolutionPrecompHom R A C E H F X Y
  let g := dgModuleResolutionPrecompHom R A C E H F Y Z
  let b := 𝟙 (moduleHom R E X.replacement.val ((H.comp F).obj Y.source))
  let c := 𝟙 (moduleHom R E X.replacement.val ((H.comp F).obj Z.source))
  have hp : (Cochain.ofHom f).comp (dgModuleFunctorResolutionPrimitive R C E F X' Y')
      (zero_add (-1)) =
    (dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y).comp
      (Cochain.ofHom b) (add_zero (-1)) := by
    simpa only [b, Cochain.comp_id] using!
      dgModuleResolutionPrecompHom_comparison R A C E H F X Y
  have ht := tensorRight_cochain_square (-1) f g b
    (dgModuleFunctorResolutionPrimitive R A E (H.comp F) X Y)
    (dgModuleFunctorResolutionPrimitive R C E F X' Y') hp
  have h := cochain_postcompose_square (-1) (f ⊗ₘ g) (b ⊗ₘ g) c
    (dgModuleFunctorResolutionFirstCompositionMap R A E (H.comp F) X Y Z)
    (dgModuleFunctorResolutionFirstCompositionMap R C E F X' Y' Z') _ _ ht
    (by simpa only [c, Category.comp_id] using!
      dgModuleResolutionPrecomp_firstCompositionMap R A C E H F X Y Z)
  simpa only [dgModuleFunctorResolutionFirstCompositePrimitive, c, Cochain.comp_id] using! h
/-- 同じ第二合成比較 cochain を全次数で保つ。 -/
lemma dgModuleResolutionPrecomp_secondPrimitive
    (X Y Z : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y)
        (dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    dgModuleFunctorResolutionSecondCompositePrimitive R A E (H.comp F) X Y Z := by
  let X' := dgModuleResolutionPrecompObject R A C E H F X
  let Y' := dgModuleResolutionPrecompObject R A C E H F Y
  let Z' := dgModuleResolutionPrecompObject R A C E H F Z
  let f := dgModuleResolutionPrecompHom R A C E H F X Y
  let g := dgModuleResolutionPrecompHom R A C E H F Y Z
  let b := 𝟙 (moduleHom R E Y.replacement.val ((H.comp F).obj Z.source))
  let c := 𝟙 (moduleHom R E X.replacement.val ((H.comp F).obj Z.source))
  have hp : (Cochain.ofHom g).comp (dgModuleFunctorResolutionPrimitive R C E F Y' Z')
      (zero_add (-1)) =
    (dgModuleFunctorResolutionPrimitive R A E (H.comp F) Y Z).comp
      (Cochain.ofHom b) (add_zero (-1)) := by
    simpa only [b, Cochain.comp_id] using!
      dgModuleResolutionPrecompHom_comparison R A C E H F Y Z
  have ht := tensorLeft_cochain_square (-1) f g b
    (dgModuleFunctorResolutionPrimitive R A E (H.comp F) Y Z)
    (dgModuleFunctorResolutionPrimitive R C E F Y' Z') hp
  have h := cochain_postcompose_square (-1) (f ⊗ₘ g) (f ⊗ₘ b) c
    (dgModuleFunctorResolutionSecondCompositionMap R A E (H.comp F) X Y Z)
    (dgModuleFunctorResolutionSecondCompositionMap R C E F X' Y' Z') _ _ ht
    (by simpa only [c, Category.comp_id] using!
      dgModuleResolutionPrecomp_secondCompositionMap R A C E H F X Y Z)
  simpa only [dgModuleFunctorResolutionSecondCompositePrimitive, c, Cochain.comp_id] using! h
/-- 同じ二項の和による合成比較 cochain を保つ。 -/
lemma dgModuleResolutionPrecomp_compositePrimitive
    (X Y Z : DGModuleFunctorResolutionObject R A E (H.comp F)) :
    (Cochain.ofHom (dgModuleResolutionPrecompHom R A C E H F X Y ⊗ₘ
      dgModuleResolutionPrecompHom R A C E H F Y Z)).comp
      (dgModuleFunctorResolutionCompositePrimitive R C E F
        (dgModuleResolutionPrecompObject R A C E H F X)
        (dgModuleResolutionPrecompObject R A C E H F Y)
        (dgModuleResolutionPrecompObject R A C E H F Z)) (zero_add (-1)) =
    dgModuleFunctorResolutionCompositePrimitive R A E (H.comp F) X Y Z := by
  rw [dgModuleFunctorResolutionCompositePrimitive, Cochain.comp_add,
    dgModuleResolutionPrecomp_firstPrimitive, dgModuleResolutionPrecomp_secondPrimitive]
  rfl
end SerrePositivity.InfinityCategories
