module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixBlockHomology
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentHomologyEdges

/-!
概要：一次 prefix の元の HA 係数を、その一単体の閉辺係数へ比較する。
方針：端点等号輸送の異種等号を合成し、Fin 2 の全体集合を二点集合に直す。
規約：coherent 入力と実辺の係数を保持する。
使われ方：prefix の実加群射をホモロジー図式の辺へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarEdgeTop_heq (t : I _⦋1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop G t)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex G t).edgeCycle 0 1 (by decide)).val := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj G t 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj G t (Fin.last 1)) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw G t)).trans ?_
  have h : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopRaw, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeCycle, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.edgeHom, h]
  rfl

lemma dgCoherentBarPrefixZeroHom_heq_edge (n : ℕ) (s : I _⦋n + 1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D G s 0 (by omega))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2).edgeCycle 0 1
        (by change (0 : Fin 2) < 1; decide)).val := by
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource_prefix R D G s 1 (by omega))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_target R D G s 0 (by omega)) rfl
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2)).trans
        (dgCoherentBarEdgeTop_heq R D G _)

lemma dgCoherentBarPrefix_one_nerve {J : Type u} [Category.{u} J] {n : ℕ}
    (s : (nerve J) _⦋n + 1⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2 =
      (CategoryTheory.nerve.edgeMk (s.map (homOfLE
        (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _)))).edge := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
