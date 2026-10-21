module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorCommaCompositionMapAssociativity
public import SerrePositivity.InfinityCategories.Derived.ComplexCochainLeftActionAssociativity
/-!
概要：同じ三重 Hom tensor 上で、三つの比較 cochain 項を括弧変更に沿って輸送する。
方針：全 cochain の結合子自然性と、三つの実作用の結合式を使う。
規約：すべて次数 −1 の全 cochain。使われ方：comma dg 圏の実結合律。
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
  (W X Y Z : DGFunctorCommaObject R C E F)
/-- 第一の実比較 cochain を、右二合成から左二合成へ輸送する。 -/
lemma dgFunctorComma_associativity_firstPrimitive :
    (Cochain.ofHom ((α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom ≫
        dgFunctorCommaHomComplex R C E F W X ◁
          dgFunctorCommaComposition R C E F X Y Z)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F W X Z) (zero_add (-1)) =
    ((tensorRightHom (dgFunctorCommaHomComplex R C E F Y Z)
      (dgFunctorCommaHomComplex R C E F W X ⊗
        dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E W.replacement (F.obj Y.source))).f (-1)
        (dgFunctorCommaFirstCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (dgFunctorCommaFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  exact tensorRight_action_cochain
    (dgFunctorCommaHomComplex R C E F W X)
    (homObject R E W.replacement (F.obj X.source))
    (dgFunctorCommaHomComplex R C E F X Y)
    (dgFunctorCommaHomComplex R C E F Y Z)
    (dgFunctorCommaHomComplex R C E F X Z)
    (homObject R E W.replacement (F.obj Y.source))
    (homObject R E W.replacement (F.obj Z.source)) (-1)
    (dgFunctorCommaPrimitive R C E F W X)
    (dgFunctorCommaComposition R C E F X Y Z)
    (dgFunctorCommaFirstCompositionMap R C E F W X Y)
    (dgFunctorCommaFirstCompositionMap R C E F W Y Z)
    (dgFunctorCommaFirstCompositionMap R C E F W X Z)
    (dgFunctorCommaFirstCompositionMap_assoc R C E F W X Y Z)
/-- 中央の実比較 cochain を、右二合成から左二合成へ輸送する。 -/
lemma dgFunctorComma_associativity_middlePrimitive :
    (Cochain.ofHom (α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (dgFunctorCommaHomComplex R C E F W X)
        (dgFunctorCommaHomComplex R C E F X Y ⊗
          dgFunctorCommaHomComplex R C E F Y Z)
        (homObject R E X.replacement (F.obj Z.source))).f (-1)
          (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (dgFunctorCommaSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) =
    ((tensorRightHom (dgFunctorCommaHomComplex R C E F Y Z)
      (dgFunctorCommaHomComplex R C E F W X ⊗
        dgFunctorCommaHomComplex R C E F X Y)
      (homObject R E W.replacement (F.obj Y.source))).f (-1)
        (dgFunctorCommaSecondCompositePrimitive R C E F W X Y)).comp
      (Cochain.ofHom (dgFunctorCommaFirstCompositionMap R C E F W Y Z))
        (add_zero (-1)) := by
  have hm : (Cochain.ofHom (𝟙 _)).comp
      (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z) (zero_add (-1)) =
      ((tensorRightHom (dgFunctorCommaHomComplex R C E F Y Z)
        (dgFunctorCommaHomComplex R C E F X Y)
        (homObject R E X.replacement (F.obj Y.source))).f (-1)
          (dgFunctorCommaPrimitive R C E F X Y)).comp
        (Cochain.ofHom (dgFunctorCommaFirstCompositionMap R C E F X Y Z))
        (add_zero (-1)) := by
    rw [Cochain.id_comp]
    rfl
  have ht := tensorCarry_cochain
    (dgFunctorCommaHomComplex R C E F W X)
    (dgFunctorCommaHomComplex R C E F X Y)
    (homObject R E X.replacement (F.obj Y.source))
    (dgFunctorCommaHomComplex R C E F Y Z)
    (dgFunctorCommaHomComplex R C E F X Y ⊗
      dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E X.replacement (F.obj Z.source))
    (homObject R E W.replacement (F.obj Y.source))
    (homObject R E W.replacement (F.obj Z.source)) (-1)
    (dgFunctorCommaPrimitive R C E F X Y)
    (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z)
    (𝟙 _) (dgFunctorCommaFirstCompositionMap R C E F X Y Z)
    (dgFunctorCommaSecondCompositionMap R C E F W X Y)
    (dgFunctorCommaSecondCompositionMap R C E F W X Z)
    (dgFunctorCommaFirstCompositionMap R C E F W Y Z) hm
    (dgFunctorCommaMixedCompositionMap_assoc R C E F W X Y Z)
  simpa only [MonoidalCategory.whiskerLeft_id, Category.comp_id] using! ht
/-- 第三の実比較 cochain を、左二合成から右二合成へ輸送する。 -/
lemma dgFunctorComma_associativity_lastPrimitive :
    (Cochain.ofHom (dgFunctorCommaComposition R C E F W X Y ▷
      dgFunctorCommaHomComplex R C E F Y Z)).comp
      (dgFunctorCommaSecondCompositePrimitive R C E F W Y Z) (zero_add (-1)) =
    (Cochain.ofHom (α_ (dgFunctorCommaHomComplex R C E F W X)
      (dgFunctorCommaHomComplex R C E F X Y)
      (dgFunctorCommaHomComplex R C E F Y Z)).hom).comp
      (((tensorLeftHom (dgFunctorCommaHomComplex R C E F W X)
        (dgFunctorCommaHomComplex R C E F X Y ⊗
          dgFunctorCommaHomComplex R C E F Y Z)
        (homObject R E X.replacement (F.obj Z.source))).f (-1)
          (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z)).comp
        (Cochain.ofHom (dgFunctorCommaSecondCompositionMap R C E F W X Z))
        (add_zero (-1))) (zero_add (-1)) := by
  exact complexCochain_tensorLeft_action_assoc
    (dgFunctorCommaHomComplex R C E F W X)
    (dgFunctorCommaHomComplex R C E F X Y)
    (dgFunctorCommaHomComplex R C E F W Y)
    (dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E Y.replacement (F.obj Z.source))
    (homObject R E X.replacement (F.obj Z.source))
    (homObject R E W.replacement (F.obj Z.source)) (-1)
    (dgFunctorCommaPrimitive R C E F Y Z)
    (dgFunctorCommaComposition R C E F W X Y)
    (dgFunctorCommaSecondCompositionMap R C E F X Y Z)
    (dgFunctorCommaSecondCompositionMap R C E F W X Z)
    (dgFunctorCommaSecondCompositionMap R C E F W Y Z)
    (dgFunctorCommaSecondCompositionMap_assoc R C E F W X Y Z)
end SerrePositivity.InfinityCategories
