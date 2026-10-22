module
public import SerrePositivity.InfinityCategories.Derived.Gluing.TwoEndpointPathPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPathEndpointSection
public import SerrePositivity.InfinityCategories.Derived.Gluing.ComplexPinchedPullback
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceFibration

/-! 同じ二端点 path の空間模型は、両端点の Kan fibration と実引き戻しを保持する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits CochainComplex DifferentialGraded HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R]

lemma dgGluingComplexPathSpaceEndpoints_fibration (Q : Complex R) :
    Fibration (complexPinchedMap.{u, v} (dgGluingComplexPathEndpoints Q)) :=
  dgGluingComplexPinchedMap_fibration _ (dgGluingComplexPathEndpoints_surjective Q)

lemma dgGluingComplexPathSpaceStart_trivialKanFibration (Q : Complex R) :
    TrivialKanFibration (complexPinchedMap.{u, v} (dgGluingComplexPathStart Q)) := by
  let : QuasiIso (dgGluingComplexPathStart Q) := dgGluingComplexPathStart_quasiIso Q
  exact complexPinchedMap_trivialKanFibration _ (complexQuasiIsoSpanLeft_surjective (𝟙 Q))

lemma dgGluingComplexPathSpaceEnd_trivialKanFibration (Q : Complex R) :
    TrivialKanFibration (complexPinchedMap.{u, v} (dgGluingComplexPathEnd Q)) := by
  let : QuasiIso (dgGluingComplexPathEnd Q) := dgGluingComplexPathEnd_quasiIso Q
  exact complexPinchedMap_trivialKanFibration _ (complexQuasiIsoSpanRight_surjective (𝟙 Q))

lemma dgGluingComplexPathSpaceConstant_equivalence (Q : Complex R) :
    IsSimplicialHomotopyEquivalence (complexPinchedMap.{u, v} (dgGluingComplexPathConstant Q)) := by
  let : QuasiIso (dgGluingComplexPathConstant Q) :=
    (complexQuasiIsoSpanLeftHomotopyEquiv (𝟙 Q)).quasiIso_inv
  exact complexPinchedMap_quasiIso_equivalence _

lemma dgGluingTwoEndpointPathSpace_isPullback {P Q : Complex R} (a b : P ⟶ Q) :
    IsPullback (complexPinchedMap.{u, v} (dgGluingCoconeTwoEndpointPath a b))
      (complexPinchedMap.{u, v} (mappingCocone.fst (b - a)))
      (complexPinchedMap.{u, v} (dgGluingComplexPathEndpoints Q))
      (complexPinchedMap.{u, v} (biprod.lift a b)) :=
  dgGluingComplexPinchedMap_isPullback (dgGluingTwoEndpointPath_isPullback a b)

end SerrePositivity.InfinityCategories
