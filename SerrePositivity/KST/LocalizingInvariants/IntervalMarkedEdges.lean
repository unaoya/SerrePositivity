module

public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators

/-!
概要：元の辺を表す区間図式は、恒等辺を含む分母集合へ全辺を送る。
方針：区間の一単体を両端の恒等と元の非退化辺の三つに分類する。
規約：元の辺そのものを保持。使われ方：Tamme 分母に沿う底変換の両側 fibration 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma interval_edge_cases (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 1 ∨
    e = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 1 ∨
    e = SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) := by
  have hm := stdSimplex.monotone_apply e (show (0 : Fin 2) ≤ 1 by decide)
  change e 0 ≤ e 1 at hm
  have hz (a : Fin 2) (ha : a ≠ 0) : a = 1 := by omega
  by_cases h₀ : e 0 = 0
  · by_cases h₁ : e 1 = 0
    · left
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> assumption
    · right; right
      have h₁' := hz (e 1) h₁
      apply SSet.stdSimplex.ext
      intro i
      fin_cases i <;> assumption
  · right; left
    have h₀' := hz (e 0) h₀
    have h₁' : e 1 = 1 := by rw [h₀'] at hm; exact le_antisymm (Fin.le_last _) hm
    apply SSet.stdSimplex.ext
    intro i
    fin_cases i <;> assumption

lemma intervalMap_edges_mem {X : SSet.{u}} (W : Set (X _⦋1⦌))
    (hW : ∀ x : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 ∈ W)
    (s : X _⦋1⦌) (hs : s ∈ W) (e : (Δ[1] : SSet.{u}) _⦋1⦌) :
    (SSet.yonedaEquiv.symm s).app (Opposite.op ⦋1⦌) e ∈ W := by
  rcases interval_edge_cases e with h | h | h
  · rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hW _
  · rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    exact hW _
  · rw [h]
    simpa only [← SSet.yonedaEquiv_comp, Category.id_comp, Equiv.apply_symm_apply] using hs

lemma invertedEdges_constant {X Y : SSet.{u}} (F : X ⟶ Y) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1 ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F := by
  have h := invertsEdges_const (Δ[1] : SSet.{u}) Y
    (F.app (Opposite.op ⦋0⦌) x) Set.univ (a := SSet.yonedaEquiv (𝟙 Δ[1])) (Set.mem_univ _)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)).map ((truncation 2).map F))
  have he : (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)).map ((truncation 2).map F))).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (F.app (Opposite.op ⦋0⦌) x) 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map _ _ _
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr h

end SerrePositivity.KST.LocalizingInvariants
