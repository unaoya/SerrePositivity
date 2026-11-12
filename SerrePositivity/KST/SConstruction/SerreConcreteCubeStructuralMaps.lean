module
public import SerrePositivity.KST.SConstruction.SerreCubeTensorUnitCoherence
public import SerrePositivity.KST.SConstruction.MonoidalUnitComparisonInverse

/-! # 元の具体的構造射の Serre 評価と単位則
概要：元の結合・左右単位の評価を次元移送として回収し、単位比較の両向きの式を得る。
方針：同じ具体的な次元同型の関手像と、元の連結鎖比較の単位則を合成する。
規約：元の関手・構造射・逆射を保持する。使われ方：Serre 関手の強モノイダル構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の具体的結合同型の関手像は、同じ次元移送。 -/
lemma serreConcreteCubeFunctor_associator (X Y Z : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeFunctor A).map (concreteCubeAssociator X Y Z).hom =
      serreCubeDimensionMap A (Nat.add_assoc X.dimension Y.dimension Z.dimension) := by
  cases X
  cases Y
  cases Z
  exact serreConcreteCubeMap_dimension A _

/-- 元の具体的左単位の関手像は、同じ次元移送。 -/
lemma serreConcreteCubeFunctor_leftUnitor (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeFunctor A).map (concreteCubeLeftUnitor X).hom =
      serreCubeDimensionMap A (Nat.zero_add X.dimension) := by
  cases X
  exact serreConcreteCubeMap_dimension A _

/-- 元の具体的右単位の関手像は、同じ次元移送。 -/
lemma serreConcreteCubeFunctor_rightUnitor (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightUnitor X).hom =
      serreCubeDimensionMap A (rfl : X.dimension + 0 = X.dimension) := by
  cases X
  exact serreConcreteCubeMap_dimension A _

/-- 元の関手の左単位の像は、元の連結鎖比較と左単位の合成。 -/
lemma serreConcreteCube_leftUnit (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeFunctor A).map (concreteCubeLeftUnitor X).hom =
      (serreCubeTensorIso A 0 X.dimension).hom ≫ (λ_ (serreCubeComonoid A X.dimension)).hom :=
  (serreConcreteCubeFunctor_leftUnitor A X).trans (serreCubeTensor_leftUnit A X.dimension)

/-- 元の関手の右単位の像は、元の連結鎖比較と右単位の合成。 -/
lemma serreConcreteCube_rightUnit (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (serreConcreteCubeFunctor A).map (concreteCubeRightUnitor X).hom =
      (serreCubeTensorIso A X.dimension 0).hom ≫ (ρ_ (serreCubeComonoid A X.dimension)).hom :=
  (serreConcreteCubeFunctor_rightUnitor A X).trans (serreCubeTensor_rightUnit A X.dimension)

/-- 元の関手と連結比較の逆左単位則。 -/
lemma serreConcreteCube_leftUnit_inv (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (λ_ (serreCubeComonoid A X.dimension)).inv =
      (serreConcreteCubeFunctor A).map (concreteCubeLeftUnitor X).inv ≫
        (serreCubeTensorIso A 0 X.dimension).hom :=
  monoidalLeftUnitComparison_inverse
    ((serreConcreteCubeFunctor A).mapIso (concreteCubeLeftUnitor X))
    (serreCubeTensorIso A 0 X.dimension).hom (serreConcreteCube_leftUnit A X)

/-- 元の関手と連結比較の逆右単位則。 -/
lemma serreConcreteCube_rightUnit_inv (X : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ConcreteCube) :
    (ρ_ (serreCubeComonoid A X.dimension)).inv =
      (serreConcreteCubeFunctor A).map (concreteCubeRightUnitor X).inv ≫
        (serreCubeTensorIso A X.dimension 0).hom :=
  monoidalRightUnitComparison_inverse
    ((serreConcreteCubeFunctor A).mapIso (concreteCubeRightUnitor X))
    (serreCubeTensorIso A X.dimension 0).hom (serreConcreteCube_rightUnit A X)

end SerrePositivity.KST.SConstruction
