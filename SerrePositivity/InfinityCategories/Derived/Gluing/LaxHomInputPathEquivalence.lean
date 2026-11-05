module
public import SerrePositivity.InfinityCategories.Derived.Gluing.ModelUnitFacesAndBoundaryFilling
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputStrictEquivalenceOfFilling
/-!
概要：指定対角境界の実充填を入力付き正本比較の実逆射と両往復変形へ接続する。
方針：二つの単位面を除いた充填を既存の固定逆射へ渡し、厳密模型と四座標模型へ移す。
規約：元左右 Hom 入力と全 path を保ち、充填や単位面の追加仮定を含めない。
使われ方：G-1 d ⑤で正本の元 pinched Hom 標的へ同値性を輸送する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

def dgGluingLaxHomDiagonalComparisonFiller :=
  (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y).choose

lemma dgGluingLaxHomDiagonalComparisonFiller_boundary :
    (boundary 2).ι ≫ dgGluingLaxHomDiagonalComparisonFiller R C D M X Y =
      dgGluingLaxHomDiagonalComparisonBoundary R C D M X Y :=
  (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y).choose_spec

def dgGluingLaxHomInputPathInverse_unit :
    SSet.Homotopy (dgGluingLaxHomInputPathComparison R C D M X Y ≫
      dgGluingLaxHomInputPathInverse R C D M X Y) (𝟙 _) :=
  dgGluingLaxHomInputPathInverse_unitOfFilling R C D M X Y
    (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y)

def dgGluingLaxHomInputPathInverse_counit :
    SSet.Homotopy (dgGluingLaxHomInputPathInverse R C D M X Y ≫
      dgGluingLaxHomInputPathComparison R C D M X Y) (𝟙 _) :=
  dgGluingLaxHomInputPathInverse_counitOfFilling R C D M X Y
    (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y)

lemma dgGluingLaxHomInputPathComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomInputPathComparison R C D M X Y) :=
  dgGluingLaxHomInputPathComparison_equivalence_of_filling R C D M X Y
    (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y)

lemma dgGluingLaxHomInputStrictComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomInputStrictComparison R C D M X Y) :=
  dgGluingLaxHomInputStrictComparison_equivalence_of_filling R C D M X Y
    (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y)

lemma dgGluingLaxHomInputCoordinateComparison_equivalence :
    IsSimplicialHomotopyEquivalence (dgGluingLaxHomInputCoordinateComparison R C D M X Y) :=
  dgGluingLaxHomInputCoordinateComparison_equivalence_of_filling R C D M X Y
    (dgGluingLaxHomDiagonalComparisonBoundary_filling R C D M X Y)
end SerrePositivity.InfinityCategories
