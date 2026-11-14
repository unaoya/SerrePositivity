module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGFunctors.DGFunctorCommaCompositionBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.ComplexTensorComparisonCochain
/-!
概要：実合成の比較 cochain の二項を、全 Hom tensor 上で構成し微分式を証明する。
方針：同じ実 primitive を左右 tensor し、実合成写像へ後合成する。
規約：全次数のパラメータを保持。使われ方：comma dg 圏の実 eComp の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] (F : DGFunctor R C E)
  (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R C E F)
/-- 実合成の比較 cochain の第一項。 -/
def dgFunctorCommaFirstCompositePrimitive :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
      (homObject R E X.replacement (F.obj Z.source)) (-1) :=
  ((tensorRightHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
    (homObject R E X.replacement (F.obj Y.source))).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)).comp
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F X Y Z)) (add_zero (-1))
/-- 実合成の比較 cochain の第二項。 -/
def dgFunctorCommaSecondCompositePrimitive :
    Cochain (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ⊗
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
      (homObject R E X.replacement (F.obj Z.source)) (-1) :=
  ((tensorLeftHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
    (homObject R E Y.replacement (F.obj Z.source))).f (-1)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)).comp
    (Cochain.ofHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F X Y Z)) (add_zero (-1))
/-- 第一項の微分は、同じ第一比較差の実合成を与える。 -/
lemma dgFunctorCommaFirstCompositePrimitive_boundary :
    δ (-1) 0 (dgFunctorCommaFirstCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y ▷
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaFirstCompositionMap R C E F X Y Z) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexComparison_rightTensor_boundary
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R C E F X Y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F Y Z)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexComparison_postcompose_boundary _ _ h _
/-- 第二項の微分も、同じ第二比較差の実合成を与える。 -/
lemma dgFunctorCommaSecondCompositePrimitive_boundary :
    δ (-1) 0 (dgFunctorCommaSecondCompositePrimitive R C E F X Y Z) +
      Cochain.ofHom ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y ◁
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F Y Z) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaSecondCompositionMap R C E F X Y Z) = 0 := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexComparison_leftTensor_boundary
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaBoundary R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaPrimitive_boundary R C E F Y Z)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCommaHomComplex R C E F X Y)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexComparison_postcompose_boundary _ _ h _
end SerrePositivity.InfinityCategories.Project.DerivedCategories
