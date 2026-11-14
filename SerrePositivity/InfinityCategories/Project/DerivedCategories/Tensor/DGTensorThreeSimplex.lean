module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTetrahedronEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveThreeSimplexCriterion
/-!
概要：二つの実三単体から、全切断和の同じ全データを持つ実 tensor 三単体を構成する。
方針：辺・三点・四点の微分式を同じ候補へ適用し、全 HA 方程式を回収する。
規約：原始元の選択は加えない。使われ方：二入力 dg nerve の tensor 構成の三次元成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 同じ全切断和のデータを保ち、全 HA 方程式を満たす実 tensor 三単体。 -/
def dgTensorThreeSimplex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (DGTensorCategory R B C) 3 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveThreeSimplex_of_equations R (DGTensorCategory R B C)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_edge_closed R B C s t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_triple_differential R B C s t)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorTetrahedronCandidate_equation R B C s t)
/-- 実 tensor 三単体の全 Hom データは、同じ全切断和候補そのものである。 -/
lemma dgTensorThreeSimplex_data (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3) :
    (dgTensorThreeSimplex R B C s t).toSimplexData =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData := rfl
/-- 実 tensor 三単体の各頂点は元の同じ二頂点の組。 -/
lemma dgTensorThreeSimplex_vertex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3) (i : Fin 4) :
    (dgTensorThreeSimplex R B C s t).obj i = (s.obj i, t.obj i) := rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
