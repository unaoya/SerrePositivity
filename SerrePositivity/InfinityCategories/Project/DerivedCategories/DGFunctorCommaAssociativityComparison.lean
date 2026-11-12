module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaAssocPrimitiveTransport
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
/-- 同じ合成比較 cochain の二つの実項への展開式。 -/
lemma dgFunctorCommaCompositePrimitive_eq
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F X Y Z =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F X Y Z +
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F X Y Z := rfl
variable (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 左先行合成の第一比較項を、前二辺の比較 cochain の和へ展開する。 -/
lemma dgFunctorComma_associativity_leftFirstExpansion :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F W X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    ((tensorRightHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E W.replacement (F.obj Y.source))).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorRightHom_ofHom, ← tensorRightHom_cochain_comp]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R C E F W X Y
  change (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F W X Y)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F W Y) (zero_add (-1)) = _ at he
  rw [he]
/-- 右先行合成の第二比較項を、後二辺の比較 cochain の和へ展開する。 -/
lemma dgFunctorComma_associativity_rightSecondExpansion :
    (Cochain.ofHom ((α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X ◁
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive R C E F W X Z) (zero_add (-1)) =
    (Cochain.ofHom (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
        (homObject R E X.replacement (F.obj Z.source))).f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) := by
  rw [Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositePrimitive,
    ← Cochain.comp_assoc_of_first_is_zero_cochain
      (Cochain.ofHom (_ ◁ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z)),
    ← tensorLeftHom_ofHom, ← tensorLeftHom_cochain_comp]
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison R C E F X Y Z
  change (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z)).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Z) (zero_add (-1)) = _ at he
  rw [he]
/-- 二つの実三重合成を比較する、同じ全 cochain の結合式。 -/
lemma dgFunctorComma_associativity_primitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F W X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    (Cochain.ofHom ((α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F W X ◁
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition R C E F X Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaCompositePrimitive R C E F W X Z) (zero_add (-1)) := by
  rw [dgFunctorCommaCompositePrimitive_eq R C E F W Y Z, Cochain.comp_add,
    dgFunctorComma_associativity_leftFirstExpansion,
    dgFunctorCommaCompositePrimitive_eq R C E F W X Y,
    map_add, Cochain.add_comp,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorComma_associativity_lastPrimitive,
    dgFunctorCommaCompositePrimitive_eq R C E F W X Z, Cochain.comp_add,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorComma_associativity_firstPrimitive,
    dgFunctorComma_associativity_rightSecondExpansion,
    dgFunctorCommaCompositePrimitive_eq R C E F X Y Z,
    map_add, Cochain.add_comp, Cochain.comp_add,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorComma_associativity_middlePrimitive]
  abel
/-- 全実二射影に加えて、二つの実三重合成の同じ比較 cochain も一致する。 -/
lemma dgFunctorComma_associativity_comparison :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F W Z _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaLeftAssociatedComposition R C E F W X Y Z) =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison R C E F W Z _
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaRightAssociatedComposition R C E F W X Y Z) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaLeftAssociatedComposition,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaRightAssociatedComposition, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComparison_precompose,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaComposition_comparison]
  exact dgFunctorComma_associativity_primitive R C E F W X Y Z
end SerrePositivity.InfinityCategories.Project.DerivedCategories
