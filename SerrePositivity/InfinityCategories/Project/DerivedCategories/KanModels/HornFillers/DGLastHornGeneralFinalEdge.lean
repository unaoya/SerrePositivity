module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.HornFillers.DGLastHornKnownCutEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGCyclePostcomposition

/-! # 一般最後外ホーンの最後の閉辺と Hom 後合成

概要：実ホーンの最後辺を閉零 cycle とし、元の Hom 複体の後合成を構成する。
方針：既知の最後右切断を二点集合へ同定し、その方程式を読む。
規約：全次元を同じ対象族で扱う。使われ方：二残差の実 Hom cone。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)

/-- 最後右切断の既知方程式から、元の最後辺の閉性を得る。 -/
lemma dgGeneralLastHornFinalEdge_closed :
    differential A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)
      (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) = 0 := by
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornKnown_rightCut σ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_pos n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornLastCut_right] at he
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.edgeHom
  rw [he]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h
  · simp [h]
  · simp [h]

/-- 同じ最後辺を、元の Hom 複体の閉零 cycle として読む。 -/
def dgGeneralLastHornFinalCycle : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject A D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2)))) :=
  ⟨_, dgGeneralLastHornFinalEdge_closed σ⟩

/-- 同じ最後辺を、元の閉零 dg 圏の実際の射として読む。 -/
def dgGeneralLastHornFinalClosed :
    ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) ⟶
      ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (Fin.last (n + 2))) :=
  (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _).symm (dgGeneralLastHornFinalCycle σ)

/-- 最後閉辺による、元の始対象からの Hom の後合成鎖写像。 -/
def dgGeneralLastHornPostcomposition :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition A D ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0) (dgGeneralLastHornFinalCycle σ)

/-- 鎖写像の全次数成分は、元の通常順斉次合成そのもの。 -/
lemma dgGeneralLastHornPostcomposition_f (k : ℤ)
    (f : GradedHom A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)) k) :
    (dgGeneralLastHornPostcomposition σ).f k f =
      compose A ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).edgeHom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate n)
        (Fin.last (n + 2)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLastHornPenultimate_lt_last n)) f (add_zero k) := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories
