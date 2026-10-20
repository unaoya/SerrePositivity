module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFunctorResolutionCompositionBoundary
public import SerrePositivity.InfinityCategories.Derived.ComplexTensorComparisonCochain
/-!
概要：実合成の比較 cochain の二項を、全 Hom tensor 上で構成し微分式を証明する。
方針：同じ実 primitive を左右 tensor し、実合成写像へ後合成する。
規約：全次数のパラメータを保持。使われ方：分解 dg 圏の実 eComp の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  (X Y Z : DGModuleFunctorResolutionObject R C E F)
/-- 実合成の比較 cochain の第一項。 -/
def dgModuleFunctorResolutionFirstCompositePrimitive :
    Cochain (dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      dgModuleFunctorResolutionHomComplex R C E F Y Z)
      (moduleHom R E X.replacement.val (F.obj Z.source)) (-1) :=
  ((tensorRightHom (dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (dgModuleFunctorResolutionHomComplex R C E F X Y)
    (moduleHom R E X.replacement.val (F.obj Y.source))).f (-1)
      (dgModuleFunctorResolutionPrimitive R C E F X Y)).comp
    (Cochain.ofHom (dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z)) (add_zero (-1))
/-- 実合成の比較 cochain の第二項。 -/
def dgModuleFunctorResolutionSecondCompositePrimitive :
    Cochain (dgModuleFunctorResolutionHomComplex R C E F X Y ⊗
      dgModuleFunctorResolutionHomComplex R C E F Y Z)
      (moduleHom R E X.replacement.val (F.obj Z.source)) (-1) :=
  ((tensorLeftHom (dgModuleFunctorResolutionHomComplex R C E F X Y)
    (dgModuleFunctorResolutionHomComplex R C E F Y Z)
    (moduleHom R E Y.replacement.val (F.obj Z.source))).f (-1)
      (dgModuleFunctorResolutionPrimitive R C E F Y Z)).comp
    (Cochain.ofHom (dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z)) (add_zero (-1))
/-- 第一項の微分は、同じ第一比較差の実合成を与える。 -/
lemma dgModuleFunctorResolutionFirstCompositePrimitive_boundary :
    δ (-1) 0 (dgModuleFunctorResolutionFirstCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom ((dgModuleFunctorResolutionBoundary R C E F X Y ▷
        dgModuleFunctorResolutionHomComplex R C E F Y Z) ≫
          dgModuleFunctorResolutionFirstCompositionMap R C E F X Y Z) = 0 := by
  have h := complexComparison_rightTensor_boundary
    (dgModuleFunctorResolutionPrimitive R C E F X Y)
    (dgModuleFunctorResolutionBoundary R C E F X Y)
    (dgModuleFunctorResolutionPrimitive_boundary R C E F X Y)
    (dgModuleFunctorResolutionHomComplex R C E F Y Z)
  exact complexComparison_postcompose_boundary _ _ h _
/-- 第二項の微分も、同じ第二比較差の実合成を与える。 -/
lemma dgModuleFunctorResolutionSecondCompositePrimitive_boundary :
    δ (-1) 0 (dgModuleFunctorResolutionSecondCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom ((dgModuleFunctorResolutionHomComplex R C E F X Y ◁
        dgModuleFunctorResolutionBoundary R C E F Y Z) ≫
          dgModuleFunctorResolutionSecondCompositionMap R C E F X Y Z) = 0 := by
  have h := complexComparison_leftTensor_boundary
    (dgModuleFunctorResolutionPrimitive R C E F Y Z)
    (dgModuleFunctorResolutionBoundary R C E F Y Z)
    (dgModuleFunctorResolutionPrimitive_boundary R C E F Y Z)
    (dgModuleFunctorResolutionHomComplex R C E F X Y)
  exact complexComparison_postcompose_boundary _ _ h _
end SerrePositivity.InfinityCategories
