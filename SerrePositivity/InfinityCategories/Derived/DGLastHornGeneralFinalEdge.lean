module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornKnownCutEquations
public import SerrePositivity.InfinityCategories.Derived.DGCyclePostcomposition

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 最後右切断の既知方程式から、元の最後辺の閉性を得る。 -/
lemma dgGeneralLastHornFinalEdge_closed :
    differential A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n)
      (Fin.last (n + 2)) (dgLastHornPenultimate_lt_last n)) = 0 := by
  have he := dgGeneralLastHornKnown_rightCut σ _ (dgLastHornPenultimate_pos n)
    (dgLastHornPenultimate_lt_last n)
  rw [dgLastHornLastCut_right] at he
  unfold SimplexData.edgeHom
  rw [he]
  unfold SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj := j.property
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h
  · simp [h]
  · simp [h]

/-- 同じ最後辺を、元の Hom 複体の閉零 cycle として読む。 -/
def dgGeneralLastHornFinalCycle : zeroCycles (homObject A D
    ((HornData.knownData σ).obj (dgLastHornPenultimate n))
    ((HornData.knownData σ).obj (Fin.last (n + 2)))) :=
  ⟨_, dgGeneralLastHornFinalEdge_closed σ⟩

/-- 最後閉辺による、元の始対象からの Hom の後合成鎖写像。 -/
def dgGeneralLastHornPostcomposition :=
  dgCyclePostcomposition A D ((HornData.knownData σ).obj 0) (dgGeneralLastHornFinalCycle σ)

/-- 鎖写像の全次数成分は、元の通常順斉次合成そのもの。 -/
lemma dgGeneralLastHornPostcomposition_f (k : ℤ)
    (f : GradedHom A ((HornData.knownData σ).obj 0)
      ((HornData.knownData σ).obj (dgLastHornPenultimate n)) k) :
    (dgGeneralLastHornPostcomposition σ).f k f =
      compose A ((HornData.knownData σ).edgeHom (dgLastHornPenultimate n)
        (Fin.last (n + 2)) (dgLastHornPenultimate_lt_last n)) f (add_zero k) := rfl

end SerrePositivity.InfinityCategories
