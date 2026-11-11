module
public import SerrePositivity.KST.SConstruction.NecklaceLambdaCell
public import SerrePositivity.KST.SConstruction.NecklaceCubicalPostcomposition

/-! # 元の単体集合写像と全 necklace Serre cell
概要：元の入力写像の Λ Hom 作用は、同じ necklace augmentation の後合成を回収する。
方針：元の cubical cell の余極限自然性に、元の Serre 鎖関手を適用する。
規約：元の necklace・全次数・両端を保持。使われ方：native HA の全単体作用素の自然性。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の入力写像の実 Λ Hom 作用は、元の同じ全 necklace cell の後合成を回収する。 -/
lemma necklaceLambdaCell_post {K L : SSet.{u}} (a : K ⟶ L) {x y : K _⦋0⦌}
    (T : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceIn K x y) :
    necklaceLambdaCell A T ≫ (cubicalLambdaMap A a).map x y =
      necklaceLambdaCell A ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.necklaceInPostcompose a x y).obj T) := by
  have h := congrArg ((cubicalSerreChains A).map) (necklaceCubicalCell_map a T)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f)
      ((cubicalSerreChains A).map_comp _ _).symm).trans
        (congrArg (fun f => (cubicalSerreChainsCubeIso A).hom.app _ ≫ f) h))

end SerrePositivity.KST.SConstruction
