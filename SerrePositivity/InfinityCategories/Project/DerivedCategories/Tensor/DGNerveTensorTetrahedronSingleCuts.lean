module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriangle
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TripleHom
/-!
概要：四頂点 tensor 候補の二つの一切断項を、元の三点 cochain と合成の tensor に同定する。
方針：交差符号を実有限集合上で評価し、同じ Hom の次数付き比較を tensor に移す。
規約：最初の内部点の項だけ負号を持つ。使われ方：三次元 HA の符号較正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
/-- 最初の内部点での切断項は、同じ三点 cochain と合成の tensor の負。 -/
lemma dgNerveTensorTetrahedronCut_first (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C 3) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {1} (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        have : j = 1 := Finset.mem_singleton.mp hj
        subst j
        decide) =
    -_root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.tripleHom 0 1 3 (by decide) (by decide))
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (t.tripleHom 1 2 3 (by decide) (by decide))
        (t.edgeHom 0 1 (by decide)) (by decide)) (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  have hsign : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (Finset.univ : Finset (Fin 4)) 0 3 {1} = 1 := by decide
  rw [hsign, Int.negOnePow_one, Units.neg_smul, one_smul,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_singleton R C t Finset.univ 0 3 1
      (by decide) _ _ (by simp) (by decide) (by decide)]
  congr 1
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom]
    exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
      _ _ _ _ ?_ ?_ _ _
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
/-- 第二内部点での切断項は、同じ三点 cochain と合成の tensor。 -/
lemma dgNerveTensorTetrahedronCut_second (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R B 3) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C 3) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {2} (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        have : j = 2 := Finset.mem_singleton.mp hj
        subst j
        decide) =
    _root_.SerrePositivity.DifferentialGraded.dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : _root_.SerrePositivity.DifferentialGraded.DGTensorCategory R B C))
      (s.tripleHom 0 2 3 (by decide) (by decide))
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := -1) (t.edgeHom 2 3 (by decide))
        (t.tripleHom 0 1 2 (by decide) (by decide)) (by decide)) (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutTerm
  dsimp only
  have hsign : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveTensorCutSign (Finset.univ : Finset (Fin 4)) 0 3 {2} = 0 := by decide
  rw [hsign, Int.negOnePow_zero, one_smul,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct_singleton R C t Finset.univ 0 3 2
      (by decide) _ _ (by simp) (by decide) (by decide)]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom]
    exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.tripleHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
      _ _ _ _ ?_ ?_ _ _
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
