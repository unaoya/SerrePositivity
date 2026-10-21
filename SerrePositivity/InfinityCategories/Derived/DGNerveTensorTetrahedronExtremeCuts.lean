module
public import SerrePositivity.InfinityCategories.Derived.DGNerveTetrahedronCutProduct
/-!
概要：四頂点 tensor 候補の空切断・全切断を、元の最高成分と辺の実 tensor へ同定する。
方針：空切断の式と三辺の実切断合成を、端点と次数を保って tensor へ移す。
規約：高次 HA の証明とは区別する。使われ方：三次元候補の四項の較正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (B : Type v) (C : Type w) [DGCategory R B] [DGCategory R C]
/-- 両内部点の切断項は第一の最高 cochain と第二の三辺の合成の tensor。 -/
lemma dgNerveTensorTetrahedronCut_all (s : SimplexData R B 3) (t : SimplexData R C 3) :
    dgNerveTensorCutTerm R B C s t Finset.univ 0 3 {1, 2} (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        rcases Finset.mem_insert.mp hj with h | h
        · subst j; decide
        · have : j = 2 := Finset.mem_singleton.mp h; subst j; decide) =
    dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
      (dgNerveTetrahedronHom R B s)
      (compose R (n := 0)
        (compose R (n := 0) (t.edgeHom 2 3 (by decide)) (t.edgeHom 1 2 (by decide)) (by decide))
        (t.edgeHom 0 1 (by decide)) (by decide)) (by decide) := by
  unfold dgNerveTensorCutTerm
  dsimp only
  have hsign : dgNerveTensorCutSign (Finset.univ : Finset (Fin 4)) 0 3 {1, 2} = 0 := by decide
  rw [hsign, Int.negOnePow_zero, one_smul, dgNerveTetrahedronCutProduct_all]
  apply eq_of_heq
  refine dgTensorElement_heq R B C rfl rfl (by decide) (by decide) rfl _ _ _ _ ?_ (HEq.refl _) _ _
  dsimp only [dgNerveTetrahedronHom]
  exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
/-- 空切断項は第一の長辺と第二の最高 cochain の tensor。 -/
lemma dgNerveTensorTetrahedronCut_empty (s : SimplexData R B 3) (t : SimplexData R C 3) :
    dgNerveTensorCutTerm R B C s t Finset.univ 0 3 ∅ (-2)
      (by decide) (by decide) ⟨by simp, fun j _ => Fin.zero_le j⟩
      ⟨by simp, fun j _ => Fin.le_last j⟩ (by simp) =
    dgTensorElement R
      (x := ((s.obj 0, t.obj 0) : DGTensorCategory R B C))
      (y := ((s.obj 3, t.obj 3) : DGTensorCategory R B C))
      (s.edgeHom 0 3 (by decide)) (dgNerveTetrahedronHom R C t) (by decide) := by
  exact dgNerveTensorCutTerm_empty R B C s t Finset.univ 0 3 (-2)
    (by decide) (by decide) _ _ (by decide)
end SerrePositivity.InfinityCategories
