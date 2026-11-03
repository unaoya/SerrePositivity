module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentableUnstraighteningEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaPresheafEvaluation
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：元の Yoneda 評価を区間写像空間上で保持する。
方針：pinched から区間への比較を外し、同じ unstraightening と恒等点評価を合成する。
規約：元の指定前層値への写像を使い、評価の同値性も二対三則で回収する。
使われ方：元の comma の区間作用の全 fiber 比較を値写像の比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)

/-- 元の表現可能前層からの区間写像を、同じ恒等点で評価する。 -/
def intervalYonedaEvaluation :=
  leftUnstraighteningMappingSpaceMap (representablePresheafInfinity x) F ≫
    (smallLeftUnstraighteningRelativeFunctorIso (representablePresheafInfinity x) F).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (representableUnstraighteningEvaluation (smallLeftUnstraighteningProjection F) x) ≫
    (smallLeftUnstraighteningLiftedFiberValueEquivalence F (SSet.opObjEquiv.symm x)).hom

/-- 同じ pinched Yoneda 評価は、元の区間作用を移してからの同じ評価。 -/
lemma yonedaPresheafEvaluation_interval :
    yonedaPresheafEvaluation x F =
      pinchedHomToIntervalMappingSpace
        (functorVertex (representablePresheafInfinity x)) (functorVertex F) ≫
          intervalYonedaEvaluation F x := by
  simp only [yonedaPresheafEvaluation, leftUnstraighteningPinchedMappingSpaceMap,
    intervalYonedaEvaluation, Category.assoc]

/-- 元の区間写像空間からの同じ指定値への評価自身が同値。 -/
lemma intervalYonedaEvaluation_isQCatEquivalence :
    IsQCatEquivalence (intervalYonedaEvaluation F x) := by
  have h := yonedaPresheafEvaluation_isQCatEquivalence x F
  rw [yonedaPresheafEvaluation_interval] at h
  exact (pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).cancel_left h

end SerrePositivity.InfinityCategories.F2.Ind
