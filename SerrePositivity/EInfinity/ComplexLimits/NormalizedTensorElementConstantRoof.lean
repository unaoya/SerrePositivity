module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementDerivedRoof
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedConstant

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
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

def normalizedTensorElementDerivedRoofFamily : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ConstantFunctorHom
    (nerve (normalizedTensorElementIndex A X Y)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
    ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
    ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y)) :=
  (complexOrdinaryDerivedConstantIso A (normalizedTensorElementIndex A X Y) X).inv ≫
    normalizedTensorElementDerivedRoof A X Y ≫
      (complexOrdinaryDerivedConstantIso A (normalizedTensorElementIndex A X Y) Y).hom

lemma normalizedTensorElementDerivedRoofFamily_triangle :
    ((normalizedTensorElementDerivedAugmentationIso A X Y).hom ≫
      (complexOrdinaryDerivedConstantIso A (normalizedTensorElementIndex A X Y) X).hom) ≫
        normalizedTensorElementDerivedRoofFamily A X Y =
    normalizedTensorElementDerivedEvaluation A X Y ≫
      (complexOrdinaryDerivedConstantIso A (normalizedTensorElementIndex A X Y) Y).hom := by
  dsimp only [normalizedTensorElementDerivedRoofFamily]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫
      (complexOrdinaryDerivedConstantIso A (normalizedTensorElementIndex A X Y) Y).hom)
      (normalizedTensorElementDerivedRoof_triangle A X Y))

end SerrePositivity.EInfinity.ComplexLimits
