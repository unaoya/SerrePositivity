module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaAssocPrimitiveTransport
/-!
概要：commaの二つの実三重合成の全比較 cochain が一致する。
方針：同じ三つの実比較項へ展開し、実作用と結合子による各項の輸送を使う。
規約：次数零に制限しない。使われ方：実comma dg 圏の結合律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 同じ合成比較 cochain の二つの実項への展開式。 -/
lemma dgFunctorCommaCompositePrimitive_eq
    (X Y Z : DGFunctorCommaObject R C E F) :
    dgFunctorCommaCompositePrimitive R C E F X Y Z =
      dgFunctorCommaFirstCompositePrimitive R C E F X Y Z +
        dgFunctorCommaSecondCompositePrimitive R C E F X Y Z := rfl
variable (W X Y Z : DGFunctorCommaObject R C E F)
/-- 左先行合成の第一比較項を、前二辺の比較 cochain の和へ展開する。 -/
lemma dgFunctorComma_associativity_leftFirstExpansion :
    (Cochain.ofHom (dgFunctorCommaComposition R C E F W X Y ▷
      dgFunctorCommaHomComplex R C E F Y Z)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    ((tensorRightHom (dgFunctorCommaHomComplex R C E F Y Z)
      (dgFunctorCommaHomComplex R C E F W X ⊗
        dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E W.replacement (F.obj Y.source))).f (-1)
        (dgFunctorCommaCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (dgFunctorCommaFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  rw [dgFunctorCommaFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
  have he := dgFunctorCommaComposition_comparison R C E F W X Y
  change (Cochain.ofHom (dgFunctorCommaComposition R C E F W X Y)).comp
    (dgFunctorCommaPrimitive R C E F W Y) (zero_add (-1)) = _ at he
  rw [he]
/-- 右先行合成の第二比較項を、後二辺の比較 cochain の和へ展開する。 -/
lemma dgFunctorComma_associativity_rightSecondExpansion :
    (Cochain.ofHom ((α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
        dgFunctorCommaHomComplex R C E F W X ◁
          dgFunctorCommaComposition R C E F X Y Z)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F W X Z) (zero_add (-1)) =
    (Cochain.ofHom (α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (dgFunctorCommaHomComplex R C E F W X)
        (dgFunctorCommaHomComplex R C E F X Y ⊗
          dgFunctorCommaHomComplex R C E F Y Z)
        (homObject R E X.replacement (F.obj Z.source))).f (-1)
          (dgFunctorCommaCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (dgFunctorCommaSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    dgFunctorCommaSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom (_ ◁ dgFunctorCommaComposition R C E F X Y Z)),
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp]
  have he := dgFunctorCommaComposition_comparison R C E F X Y Z
  change (Cochain.ofHom (dgFunctorCommaComposition R C E F X Y Z)).comp
    (dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) = _ at he
  rw [he]
/-- 二つの実三重合成を比較する、同じ全 cochain の結合式。 -/
lemma dgFunctorComma_associativity_primitive :
    (Cochain.ofHom (dgFunctorCommaComposition R C E F W X Y ▷
      dgFunctorCommaHomComplex R C E F Y Z)).comp
      (dgFunctorCommaCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    (Cochain.ofHom ((α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
        dgFunctorCommaHomComplex R C E F W X ◁
          dgFunctorCommaComposition R C E F X Y Z)).comp
      (dgFunctorCommaCompositePrimitive R C E F W X Z) (zero_add (-1)) := by
  rw [dgFunctorCommaCompositePrimitive_eq R C E F W Y Z, Cochain.comp_add,
    dgFunctorComma_associativity_leftFirstExpansion,
    dgFunctorCommaCompositePrimitive_eq R C E F W X Y,
    map_add, Cochain.add_comp,
    dgFunctorComma_associativity_lastPrimitive,
    dgFunctorCommaCompositePrimitive_eq R C E F W X Z, Cochain.comp_add,
    dgFunctorComma_associativity_firstPrimitive,
    dgFunctorComma_associativity_rightSecondExpansion,
    dgFunctorCommaCompositePrimitive_eq R C E F X Y Z,
    map_add, Cochain.add_comp, Cochain.comp_add,
    dgFunctorComma_associativity_middlePrimitive]
  abel
/-- 全実二射影に加えて、二つの実三重合成の同じ比較 cochain も一致する。 -/
lemma dgFunctorComma_associativity_comparison :
    dgFunctorCommaHomComparison R C E F W Z _
      (dgFunctorCommaLeftAssociatedComposition R C E F W X Y Z) =
    dgFunctorCommaHomComparison R C E F W Z _
      (dgFunctorCommaRightAssociatedComposition R C E F W X Y Z) := by
  rw [dgFunctorCommaLeftAssociatedComposition,
    dgFunctorCommaRightAssociatedComposition, ← Category.assoc,
    dgFunctorCommaHomComparison_precompose,
    dgFunctorCommaHomComparison_precompose,
    dgFunctorCommaComposition_comparison,
    dgFunctorCommaComposition_comparison]
  exact dgFunctorComma_associativity_primitive R C E F W X Y Z
end SerrePositivity.InfinityCategories
