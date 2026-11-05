module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxCoordinateComparison
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Derived.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Derived.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Derived.Gluing.IntervalPostEndpointNaturality
/-!
概要：元 lax Hom 標的への指定比較自身の実逆と両往復ホモトピーを構成する。
方針：同じ実比較の全射影・端点輸送・全入力を保持する。
規約：新たな主経路仮定を置かない。使われ方：K-S• の全 lax 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomPullbackComparison_equivalence :
    IsSimplicialHomotopyEquivalence
      (dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) := by
  letI := dgGluingHomTargetLaxHomPullback_kanComplex R C D E p q X Y
  letI := dgGluingHomTargetInputStrictPullback_kanComplex R C D E p q X Y
  have hcoord : KanComplex (dgGluingHomTargetInputCoordinateTarget R C D E p q X Y) :=
    isFibrant_of_fibration (dgGluingHomTargetInputStrictCoordinatesIso R C D E p q X Y).inv
  letI := hcoord
  apply (dgGluingHomTargetLaxHomCoordinateTransport_equivalence R C D E p q X Y).cancel_right
  rw [dgGluingHomTargetLaxHomCoordinateTransport_comparison]
  exact dgGluingHomTargetInputCoordinateComparison_equivalence R C D E p q X Y

def dgGluingHomTargetLaxHomPullbackComparisonInverse :=
  (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y).choose

def dgGluingHomTargetLaxHomPullbackComparisonInverse_unit :
    SSet.Homotopy (dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomPullbackComparisonInverse R C D E p q X Y) (𝟙 _) :=
  (Classical.choose_spec
    (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y)).1.some

def dgGluingHomTargetLaxHomPullbackComparisonInverse_counit :
    SSet.Homotopy (dgGluingHomTargetLaxHomPullbackComparisonInverse R C D E p q X Y ≫
      dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) (𝟙 _) :=
  (Classical.choose_spec
    (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y)).2.some

end SerrePositivity.InfinityCategories
