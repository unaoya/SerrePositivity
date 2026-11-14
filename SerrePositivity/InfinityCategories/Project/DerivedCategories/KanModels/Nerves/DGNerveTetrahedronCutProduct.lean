module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGNerveTensorTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveTetrahedronBoundary
/-!
概要：四頂点の全内部切断の合成は元の三辺の合成に一致する。
方針：二点の昇順列の再帰を一段だけ展開し、一切断の式と全 Hom の比較を使う。
規約：再帰全体の simp 展開を避ける。使われ方：tensor 最高成分の三次元較正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
/-- 両内部点で区切る実合成は、元の三辺の通常順合成に一致する。 -/
lemma dgNerveTetrahedronCutProduct_all (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D 3) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct R D s Finset.univ 0 3 {1, 2} (by decide)
      ⟨by simp, fun j _ => Fin.zero_le j⟩ ⟨by simp, fun j _ => Fin.le_last j⟩ (by
        intro j hj
        rcases Finset.mem_insert.mp hj with h | h
        · subst j; decide
        · have : j = 2 := Finset.mem_singleton.mp h; subst j; decide) =
    _root_.SerrePositivity.DifferentialGraded.compose R (n := 0)
      (_root_.SerrePositivity.DifferentialGraded.compose R (n := 0) (s.edgeHom 2 3 (by decide)) (s.edgeHom 1 2 (by decide)) (by decide))
      (s.edgeHom 0 1 (by decide)) (by decide) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCutProduct
  simp only [show (({1, 2} : Finset (Fin 4)).sort (· ≤ ·)) = [1, 2] from by
    rw [Finset.sort_insert (· ≤ ·) (by
      intro b hb
      have : b = 2 := Finset.mem_singleton.mp hb
      subst b
      decide) (by decide), Finset.sort_singleton]]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct]
  dsimp only [List.casesOn]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveListCutProduct_singleton R D s
    ((Finset.univ : Finset (Fin 4)).filter (1 ≤ ·)) 1 3 2
    (2 - (((Finset.univ : Finset (Fin 4)).filter (1 ≤ ·)).card : ℤ) + ([2].length : ℤ))
    (by simp) _ _ _ (by decide) (by decide) (by decide)]
  apply eq_of_heq
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
    _ _ _ _ ?_ ?_ _ _
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) rfl rfl rfl (by decide) (by decide) (by decide)
      _ _ _ _ ?_ ?_ _ _
    · exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
    · exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
  · dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom]
    exact s.hom_heq_of_indices_degree (by decide) rfl rfl (by decide)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
