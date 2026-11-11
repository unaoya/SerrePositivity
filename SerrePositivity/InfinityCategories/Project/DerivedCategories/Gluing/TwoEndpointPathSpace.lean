module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TwoEndpointPathPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPathEndpointSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ComplexPinchedPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconePathSpaceFibration

/-! 同じ二端点 path の空間模型は、両端点の Kan fibration と実引き戻しを保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits CochainComplex DifferentialGraded HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPathSpaceEndpoints_fibration (Q : Complex R) :
    Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedMap_fibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints_surjective Q)

lemma dgGluingComplexPathSpaceStart_trivialKanFibration (Q : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q)) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart Q) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathStart_quasiIso Q
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeft_surjective (𝟙 Q))

lemma dgGluingComplexPathSpaceEnd_trivialKanFibration (Q : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q)) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd Q) := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEnd_quasiIso Q
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_trivialKanFibration _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanRight_surjective (𝟙 Q))

lemma dgGluingComplexPathSpaceConstant_equivalence (Q : Complex R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathConstant Q)) := by
  let : QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathConstant Q) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexQuasiIsoSpanLeftHomotopyEquiv (𝟙 Q)).quasiIso_inv
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap_quasiIso_equivalence _

lemma dgGluingTwoEndpointPathSpace_isPullback {P Q : Complex R} (a b : P ⟶ Q) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconeTwoEndpointPath a b))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (mappingCocone.fst (b - a)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPathEndpoints Q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (biprod.lift a b)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingComplexPinchedMap_isPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTwoEndpointPath_isPullback a b)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
