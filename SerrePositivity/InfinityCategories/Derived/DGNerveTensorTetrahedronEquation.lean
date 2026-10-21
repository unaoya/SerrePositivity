module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorTriple
public import SerrePositivity.InfinityCategories.Derived.DGTensorGradedComposition
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorTetrahedronExpansion
public import SerrePositivity.InfinityCategories.DGNerve.Residual
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 元の二実三単体から作った候補の最高成分は、同じ候補の HA 微分式を満たす。 -/
lemma dgNerveTensorTetrahedronCandidate_equation (s : Simplex R B 3) (t : Simplex R C 3) :
    differential R (dgNerveTetrahedronHom R (DGTensorCategory R B C)
      (dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData)) =
    (dgNerveTensorDataCandidate R B C s.toSimplexData t.toSimplexData).rhs
      Finset.univ 0 3 (-2) (by decide) (by decide) (by decide) (by decide) := by
  change differential R (dgNerveTensorHomCandidate R B C s.toSimplexData t.toSimplexData
      Finset.univ 0 3 (-2) (by decide) (by decide)
      ⟨by simp, fun j _ => Fin.zero_le j⟩ ⟨by simp, fun j _ => Fin.le_last j⟩) = _
  rw [dgNerveTensorTetrahedronCandidate_top, dgNerveTetrahedron_rhs]
  simp only [dgNerveTensorDataCandidate_tripleHom, dgNerveTensorDataCandidate_edgeHom]
  simp only [compose_add_left, compose_add_right, dgTensorElement_compose R B C]
  simp only [differential_add, differential_sub, dgTensorElement_differential R B C,
    dgNerveTetrahedronHom_differential, dgNerveTripleHom_differential,
    differential_compose, dgNerveData_edgeHom_differential R B s 0 3 (by decide),
    dgNerveData_edgeHom_differential R C t 0 1 (by decide),
    dgNerveData_edgeHom_differential R C t 1 2 (by decide),
    dgNerveData_edgeHom_differential R C t 2 3 (by decide)]
  norm_num [Int.negOnePow_neg, Int.negOnePow_even (-2) ⟨-1, rfl⟩]
  simp only [zero_compose, compose_zero, add_zero, zero_add,
    dgTensorElement_zero_left R B C, dgTensorElement_zero_right R B C,
    dgTensorElement_add_left R B C, dgTensorElement_add_right R B C,
    dgTensorElement_sub_left R B C,
    dgTensorElement_sub_right R B C, compose_sub_left, compose_sub_right, compose_assoc]
  simp only [Simplex.edgeHom, SimplexData.edgeHom]
  have hz := dgTensorElement_zero_right R B C
    (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
    (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C)) (q := 0) (n := -1)
    (s.toSimplexData.tripleHom 0 1 3 (by decide) (by decide)) (by decide)
  simp only [neg_zero, add_zero, hz]
  abel
end SerrePositivity.InfinityCategories
