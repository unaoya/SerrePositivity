module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriple
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTetrahedronExpansion
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual
/-!
概要：四項で表した tensor 候補の最高成分は、同じ候補の HA 右辺を微分に持つ。
方針：三点微分式と辺の閉性・Leibniz 則・実 tensor 合成式を使い、全項を相殺する。
規約：三次元で全ての実 cochain と符号を照合する。使われ方：実 tensor 三単体への昇格。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 元の二実三単体から作った候補の最高成分は、同じ候補の HA 微分式を満たす。 -/
lemma dgNerveTensorTetrahedronCandidate_equation (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R C 3) :
    differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTetrahedronHom R (DGTensorCategory R B C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData)) =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).rhs
      Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) := by
  change differential R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      Finset.univ 0 3 (-2) (by decide) (by decide)
      ⟨by simp, fun j _ => Fin.zero_le j⟩ ⟨by simp, fun j _ => Fin.le_last j⟩) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorTetrahedronCandidate_top, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTetrahedron_rhs]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_tripleHom, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorDataCandidate_edgeHom]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_right, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_compose R B C]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_add, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_differential R B C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTetrahedronHom_differential, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTripleHom_differential,
    differential_compose, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveData_edgeHom_differential R B s 0 3 (by decide),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveData_edgeHom_differential R C t 0 1 (by decide),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveData_edgeHom_differential R C t 1 2 (by decide),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveData_edgeHom_differential R C t 2 3 (by decide)]
  norm_num [Int.negOnePow_neg, Int.negOnePow_even (-2) ⟨-1, rfl⟩]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, add_zero, zero_add,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_left R B C, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_right R B C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_add_left R B C, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_add_right R B C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_sub_left R B C,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_sub_right R B C, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right, compose_assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
  have hz := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_zero_right R B C
    (x := ((s.obj 0, t.obj 0) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
    (y := ((s.obj 3, t.obj 3) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C)) (q := 0) (n := -1)
    (s.toSimplexData.tripleHom 0 1 3 (by decide) (by decide)) (by decide)
  simp only [neg_zero, add_zero, hz]
  abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories
