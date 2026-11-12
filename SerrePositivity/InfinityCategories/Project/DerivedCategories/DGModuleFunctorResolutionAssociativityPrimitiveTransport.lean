module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionCompositionMapAssociativity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ComplexCochainLeftActionAssociativity
/-!
概要：同じ三重 Hom tensor 上で、三つの比較 cochain 項を括弧変更に沿って輸送する。
方針：全 cochain の結合子自然性と、三つの実作用の結合式を使う。
規約：すべて次数 −1 の全 cochain。使われ方：分解 dg 圏の実結合律。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (W X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)
/-- 第一の実比較 cochain を、右二合成から左二合成へ輸送する。 -/
lemma dgModuleFunctorResolution_associativity_firstPrimitive :
    (Cochain.ofHom ((α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X ◁
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F X Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F W X Z) (zero_add (-1)) =
    ((tensorRightHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
      (moduleHom R E W.replacement.val (F.obj Y.source))).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  exact tensorRight_action_cochain
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
    (moduleHom R E W.replacement.val (F.obj X.source))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Z)
    (moduleHom R E W.replacement.val (F.obj Y.source))
    (moduleHom R E W.replacement.val (F.obj Z.source)) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F W X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W X Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap_assoc R C E F W X Y Z)
/-- 中央の実比較 cochain を、右二合成から左二合成へ輸送する。 -/
lemma dgModuleFunctorResolution_associativity_middlePrimitive :
    (Cochain.ofHom (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
        (moduleHom R E X.replacement.val (F.obj Z.source))).f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) =
    ((tensorRightHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X ⊗
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
      (moduleHom R E W.replacement.val (F.obj Y.source))).f (-1)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  have hm : (Cochain.ofHom (𝟙 _)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z) (zero_add (-1)) =
      ((tensorRightHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
        (moduleHom R E X.replacement.val (F.obj Y.source))).f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z))
        (add_zero (-1)) := by
    rw [Cochain.id_comp]
    rfl
  have ht := tensorCarry_cochain
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
    (moduleHom R E X.replacement.val (F.obj Y.source))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (moduleHom R E X.replacement.val (F.obj Z.source))
    (moduleHom R E W.replacement.val (F.obj Y.source))
    (moduleHom R E W.replacement.val (F.obj Z.source)) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z)
    (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionFirstCompositionMap R C E F W Y Z) hm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionMixedCompositionMap_assoc R C E F W X Y Z)
  simpa only [MonoidalCategory.whiskerLeft_id, Category.comp_id] using! ht
/-- 第三の実比較 cochain を、左二合成から右二合成へ輸送する。 -/
lemma dgModuleFunctorResolution_associativity_lastPrimitive :
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F W X Y ▷
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    (Cochain.ofHom (α_ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
        (moduleHom R E X.replacement.val (F.obj Z.source))).f (-1)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexCochain_tensorLeft_action_assoc
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W X)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F W Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (moduleHom R E Y.replacement.val (F.obj Z.source))
    (moduleHom R E X.replacement.val (F.obj Z.source))
    (moduleHom R E W.replacement.val (F.obj Z.source)) (-1)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionPrimitive R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionComposition R C E F W X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W X Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap R C E F W Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSecondCompositionMap_assoc R C E F W X Y Z)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
