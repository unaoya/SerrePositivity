module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTensorTriangle
public import SerrePositivity.InfinityCategories.DGNerve.TripleHom
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 最初の内部点での切断項は、同じ三点 cochain と合成の tensor の負。 -/
lemma dgNerveTensorTetrahedronCut_first (s : SimplexData R B 3) (t : SimplexData R C 3) :
    dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {1} (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        have : j = 1 := Finset.mem_singleton.mp hj
        subst j
        decide) =
    -dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
      (s.tripleHom 0 1 3 (by decide) (by decide))
      (compose R (n := -1) (t.tripleHom 1 2 3 (by decide) (by decide))
        (t.edgeHom 0 1 (by decide)) (by decide)) (by decide) := by
  unfold dgNerveTensorCutTerm
  dsimp only
  have hsign : dgNerveTensorCutSign (Finset.univ : Finset (Fin 4)) 0 3 {1} = 1 := by decide
  rw [hsign, Int.negOnePow_one, Units.neg_smul, one_smul,
    dgNerveCutProduct_singleton R C t Finset.univ 0 3 1
      (by decide) _ _ (by simp) (by decide) (by decide)]
  congr 1
  apply eq_of_heq
  refine dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [SimplexData.tripleHom]
    exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
  · dsimp only [SimplexData.tripleHom, SimplexData.edgeHom]
    refine gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
      _ _ _ _ ?_ ?_ _ _
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
/-- 第二内部点での切断項は、同じ三点 cochain と合成の tensor。 -/
lemma dgNerveTensorTetrahedronCut_second (s : SimplexData R B 3) (t : SimplexData R C 3) :
    dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {2} (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        have : j = 2 := Finset.mem_singleton.mp hj
        subst j
        decide) =
    dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
      (s.tripleHom 0 2 3 (by decide) (by decide))
      (compose R (n := -1) (t.edgeHom 2 3 (by decide))
        (t.tripleHom 0 1 2 (by decide) (by decide)) (by decide)) (by decide) := by
  unfold dgNerveTensorCutTerm
  dsimp only
  have hsign : dgNerveTensorCutSign (Finset.univ : Finset (Fin 4)) 0 3 {2} = 0 := by decide
  rw [hsign, Int.negOnePow_zero, one_smul,
    dgNerveCutProduct_singleton R C t Finset.univ 0 3 2
      (by decide) _ _ (by simp) (by decide) (by decide)]
  apply eq_of_heq
  refine dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ ?_ _ _
  · dsimp only [SimplexData.tripleHom]
    exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
  · dsimp only [SimplexData.tripleHom, SimplexData.edgeHom]
    refine gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
      _ _ _ _ ?_ ?_ _ _
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact t.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
end SerrePositivity.InfinityCategories
