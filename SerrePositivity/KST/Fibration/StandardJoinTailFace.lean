module
public import SerrePositivity.KST.Fibration.StandardTailVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitExamples

/-! # 標準 join の右因子の始点と元の最後の面射の照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 標準 join の左因子の元の頂点番号は変わらない。 -/
lemma standardJoin_inl_vertex (n m : ℕ) (j : Fin (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[m] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n m).hom).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) =
        stdSimplex.obj₀Equiv.symm ⟨j.val, by omega⟩ := by
  apply stdSimplex.ext
  intro a
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat (p := n + 1) (q := m + 1) (r := 1) 1 (by omega)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} n 1 (stdSimplex.obj₀Equiv.{u}.symm j))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv.{u} m 0 PUnit.unit) a).val = j.val
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ a.isLt]
  rfl

/-- 右因子の元の始点に制限した標準 join は、元の長い単体の最後の面である。 -/
lemma standardJoin_right_initial_face (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[n] : SSet.{u})) (stdSimplex.δ (1 : Fin 2)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ stdSimplex.δ (Fin.last (n + 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitChecks.join_hom_ext_to_stdSimplex
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap_assoc, Category.id_comp, ← Category.assoc]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro v
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom).app _ _) =
      (stdSimplex.δ (Fin.last (n + 2))).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom).app _ _)
    rw [standardJoin_inl_vertex, standardJoin_inl_vertex]
    apply stdSimplex.ext
    intro a
    apply Fin.ext
    change j.val = ((Fin.last (n + 2)).succAbove ⟨j.val, by omega⟩).val
    simp
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap_assoc, ← Category.assoc]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
    apply ConcreteCategory.hom_ext
    intro v
    obtain ⟨j, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    have hj : j = 0 := Fin.eq_zero j
    subst j
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 1).hom).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      (stdSimplex.δ (Fin.last (n + 2))).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom).app _
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    rw [joinStdSimplexIso_inr_vertex, joinStdSimplexIso_inr_vertex]
    apply stdSimplex.ext
    intro a
    apply Fin.ext
    change n + 1 + 0 = ((Fin.last (n + 2)).succAbove ⟨n + 1 + 0, by omega⟩).val
    simp

end SerrePositivity.KST.Fibration
