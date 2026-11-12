module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxCoordinateComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxRawInputActions
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetLaxBaseCoordinates
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomTargetInputStrictEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RestrictedDiagonalInputPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.EndpointTransportComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ArrowIntervalCompositionEndpoints
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.IntervalPostEndpointNaturality
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet KST.SConstruction
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
  (p : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) (q : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E)
local notation "M" => dgHomGluingBimodule R C D E p q
variable (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetHomParameter R C D E p q X Y
local notation "eX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q X
local notation "eY" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetAugmentationEdge R C D E p q Y
attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetLaxHomPullbackComparison_equivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullback_kanComplex R C D E p q X Y
  letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputStrictPullback_kanComplex R C D E p q X Y
  have hcoord : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateTarget R C D E p q X Y) :=
    isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputStrictCoordinatesIso R C D E p q X Y).inv
  letI := hcoord
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport_equivalence R C D E p q X Y).cancel_right
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomCoordinateTransport_comparison]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetInputCoordinateComparison_equivalence R C D E p q X Y

def dgGluingHomTargetLaxHomPullbackComparisonInverse :=
  (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y).choose

def dgGluingHomTargetLaxHomPullbackComparisonInverse_unit :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y ≫
      dgGluingHomTargetLaxHomPullbackComparisonInverse R C D E p q X Y) (𝟙 _) :=
  (Classical.choose_spec
    (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y)).1.some

def dgGluingHomTargetLaxHomPullbackComparisonInverse_counit :
    SSet.Homotopy (dgGluingHomTargetLaxHomPullbackComparisonInverse R C D E p q X Y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomTargetLaxHomPullbackComparison R C D E p q X Y) (𝟙 _) :=
  (Classical.choose_spec
    (dgGluingHomTargetLaxHomPullbackComparison_equivalence R C D E p q X Y)).2.some

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
