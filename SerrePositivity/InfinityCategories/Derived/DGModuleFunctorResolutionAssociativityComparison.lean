module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionAssociativityPrimitiveTransport
/-!
概要：出力分解の二つの実三重合成の全比較 cochain が一致する。
方針：同じ三つの実比較項へ展開し、実作用と結合子による各項の輸送を使う。
規約：次数零に制限しない。使われ方：実分解 dg 圏の結合律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
/-- 同じ合成比較 cochain の二つの実項への展開式。 -/
lemma dgModuleFunctorResolutionCompositePrimitive_eq
    (X Y Z : DGModuleFunctorResolutionObject R C E F) :
    dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z =
      dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z +
        dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z := rfl
variable (W X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 左先行合成の第一比較項を、前二辺の比較 cochain の和へ展開する。 -/
lemma dgModuleFunctorResolution_associativity_leftFirstExpansion :
    (Cochain.ofHom (dgModuleFunctorResolutionComposition R C E F W X Y ▷
      dgModuleFunctorResolutionHomComplex R C E F Y Z)).comp
      (dgModuleFunctorResolutionFirstCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    ((tensorRightHom (dgModuleFunctorResolutionHomComplex R C E F Y Z)
      (dgModuleFunctorResolutionHomComplex R C E F W X ⊗
        dgModuleFunctorResolutionHomComplex R C E F X Y)
      (moduleHom R E W.replacement.val (F.obj Y.source))).f (-1)
        (dgModuleFunctorResolutionCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  rw [dgModuleFunctorResolutionFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
  have he := dgModuleFunctorResolutionComposition_comparison R C E F W X Y
  change (Cochain.ofHom (dgModuleFunctorResolutionComposition R C E F W X Y)).comp
    (dgModuleFunctorResolutionPrimitive R C E F W Y) (zero_add (-1)) = _ at he
  rw [he]
/-- 右先行合成の第二比較項を、後二辺の比較 cochain の和へ展開する。 -/
lemma dgModuleFunctorResolution_associativity_rightSecondExpansion :
    (Cochain.ofHom ((α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
      (dgModuleFunctorResolutionHomComplex R C E F X Y)
      (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
        dgModuleFunctorResolutionHomComplex R C E F W X ◁
          dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
      (dgModuleFunctorResolutionSecondCompositePrimitive R C E F W X Z) (zero_add (-1)) =
    (Cochain.ofHom (α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
      (dgModuleFunctorResolutionHomComplex R C E F X Y)
      (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (dgModuleFunctorResolutionHomComplex R C E F W X)
        (dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
          dgModuleFunctorResolutionHomComplex R C E F Y Z)
        (moduleHom R E X.replacement.val (F.obj Z.source))).f (-1)
          (dgModuleFunctorResolutionCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    dgModuleFunctorResolutionSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom (_ ◁ dgModuleFunctorResolutionComposition R C E F X Y Z)),
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp]
  have he := dgModuleFunctorResolutionComposition_comparison R C E F X Y Z
  change (Cochain.ofHom (dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
    (dgModuleFunctorResolutionPrimitive R C E F X Z) (zero_add (-1)) = _ at he
  rw [he]
/-- 二つの実三重合成を比較する、同じ全 cochain の結合式。 -/
lemma dgModuleFunctorResolution_associativity_primitive :
    (Cochain.ofHom (dgModuleFunctorResolutionComposition R C E F W X Y ▷
      dgModuleFunctorResolutionHomComplex R C E F Y Z)).comp
      (dgModuleFunctorResolutionCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    (Cochain.ofHom ((α_ (dgModuleFunctorResolutionHomComplex R C E F W X)
      (dgModuleFunctorResolutionHomComplex R C E F X Y)
      (dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
        dgModuleFunctorResolutionHomComplex R C E F W X ◁
          dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
      (dgModuleFunctorResolutionCompositePrimitive R C E F W X Z) (zero_add (-1)) := by
  rw [dgModuleFunctorResolutionCompositePrimitive_eq R C E F W Y Z, Cochain.comp_add,
    dgModuleFunctorResolution_associativity_leftFirstExpansion,
    dgModuleFunctorResolutionCompositePrimitive_eq R C E F W X Y,
    map_add, Cochain.add_comp,
    dgModuleFunctorResolution_associativity_lastPrimitive,
    dgModuleFunctorResolutionCompositePrimitive_eq R C E F W X Z, Cochain.comp_add,
    dgModuleFunctorResolution_associativity_firstPrimitive,
    dgModuleFunctorResolution_associativity_rightSecondExpansion,
    dgModuleFunctorResolutionCompositePrimitive_eq R C E F X Y Z,
    map_add, Cochain.add_comp, Cochain.comp_add,
    dgModuleFunctorResolution_associativity_middlePrimitive]
  abel
/-- 全実二射影に加えて、二つの実三重合成の同じ比較 cochain も一致する。 -/
lemma dgModuleFunctorResolution_associativity_comparison :
    dgModuleFunctorResolutionHomComparison R C E F W Z _
      (dgModuleFunctorResolutionLeftAssociatedComposition R C E F W X Y Z) =
    dgModuleFunctorResolutionHomComparison R C E F W Z _
      (dgModuleFunctorResolutionRightAssociatedComposition R C E F W X Y Z) := by
  rw [dgModuleFunctorResolutionLeftAssociatedComposition,
    dgModuleFunctorResolutionRightAssociatedComposition, ← Category.assoc,
    dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionHomComparison_precompose,
    dgModuleFunctorResolutionComposition_comparison,
    dgModuleFunctorResolutionComposition_comparison]
  exact dgModuleFunctorResolution_associativity_primitive R C E F W X Y Z
end SerrePositivity.InfinityCategories
