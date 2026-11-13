module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackExactProjections

/-!
概要：安定圏間の完全関手の lax pullback の全ての射は cofiber 四角形を持つ。
方針：選んだ零対象への辺を指定したまま span の余極限を作り、四角形へ戻す。
規約：元の射は四角形の下辺として厳密に保持する。
使われ方：Tamme Lemma 8(iv) の安定性の cofiber 存在条件。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
variable [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable A] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] (p : A ⟶ C) (q : B ⟶ C)
variable [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor p] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor q]

/-- 概要：lax pullback の元の指定射の cofiber 四角形が存在する。
方針：指定射と零対象への辺の span を保つ余極限から四角形を構成する。
規約：lax pullback の安定性や全有限余極限は仮定しない。
使われ方：安定性の定義の cofiber_exists。 -/
lemma laxPullback_cofiber_exists {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)) x y) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q)
  let g := Classical.choice (z.isTerminal.nonempty_edge x)
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f g).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]
    have hg : (SSet.yonedaEquiv.symm g.edge).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = z.vertex := by
      have hv : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
          (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
        apply SSet.yonedaEquiv.injective
        decide
      have he := congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSimplex_target g)
      rw [← hv, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply] at he
      exact he
    exact hg.symm ▸ z.isZero
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.hasColimit_laxPullback_span_of_zero_second p q (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f g) hz
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c = SSet.yonedaEquiv.symm f.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_bottom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_left]
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c = SSet.yonedaEquiv.symm g.edge := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_left, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan_right]
  have hzero : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c) 0 1 = z.vertex := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftEdge_target, hg]
    exact (congrArg (fun v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) _⦋1⦌ => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q).δ 0 v)
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q) (n := ⦋1⦌)).apply_symm_apply g.edge)).trans
        g.tgt_eq
  exact ⟨{ square := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare c
           zero_corner := hzero.symm ▸ z.isZero
           bottom_edge := he
           isPushout := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.coconeSquare_isPushout c hc }⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
