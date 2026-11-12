module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixEdgeRaw

/-!
概要：一次 prefix の閉零係数と、元のホモロジー図式で使う辺の係数の異種等号。
方針：同じ nerve の最初の辺を universe 持上げして G へ送り、HA 係数を比較する。
規約：元の coherent 辺と端点輸送を保持する。
使われ方：prefix のホモロジー射を H(G) の実関手の射へ合わせる。
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
  {J : Type u} [Category.{u} J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixZeroHom_heq_diagramEdge {n : ℕ} (s : (nerve J) _⦋n + 1⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixHom R D G s 0 (by omega))
      (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarDiagramEdge R D G (s.map (homOfLE
          (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _)))))).val := by
  let f := s.map (homOfLE (show (0 : Fin (n + 2)) ≤ ⟨1, by omega⟩ from Fin.zero_le _))
  let E := ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.up.{u, max (u + 1) v} (X := nerve J)
    (CategoryTheory.nerve.edgeMk f).toTruncated).map ((SSet.truncation 2).map G))
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2 = E.edge := by
    change G.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2) =
      G.app _ (ULift.up (CategoryTheory.nerve.edgeMk f).edge)
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefix_one_nerve]
    rfl
  refine (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarPrefixZeroHom_heq_edge R D G n s).trans ?_
  have hr : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix s 1 (by omega)).2).edgeCycle
      0 1 (by change (0 : Fin 2) < 1; decide)).val (E.edge.edgeCycle 0 1 (by decide)).val := by
    rw [ht]
  refine hr.trans ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeCycle_val_heq E).symm.trans ?_)
  exact heq_of_eq (congrArg Subtype.val (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.edgeClosed_cycle E)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
