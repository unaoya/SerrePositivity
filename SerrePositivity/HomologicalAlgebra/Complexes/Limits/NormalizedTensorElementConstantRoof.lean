module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorElementDerivedRoof
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedConstant

/-!
概要：同じ全単体の実導来屋根の両端を元の頂点の定値図式へ戻す。
方針：同じ通常定値図式との端点等式を全関手圏の同型で輸送する。
規約：元の全 augmentation・評価円柱を保つ。
使われ方：元の正規化 Hom の終端 augmentation に沿う大域評価との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementDerivedRoofFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom
    (nerve (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
    ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
    ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) X).inv ≫
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof A X Y ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) Y).hom

lemma normalizedTensorElementDerivedRoofFamily_triangle :
    ((_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedAugmentationIso A X Y).hom ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) X).hom) ≫
        _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily A X Y =
    _root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedEvaluation A X Y ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) Y).hom := by
  dsimp only [_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoofFamily]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedConstantIso A (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementIndex A X Y) Y).hom)
      (_root_.SerrePositivity.ComplexLimits.normalizedTensorElementDerivedRoof_triangle A X Y))

end SerrePositivity.ComplexLimits
