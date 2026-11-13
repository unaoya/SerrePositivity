module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PathMaximumCylinder

/-!
# 最大座標円柱の元の時間の両端

概要：時刻零の全図式と始点が時刻一の場合の全 path の時間を計算する。
方針：元の時間の単調性と始点以下にならない最大座標を使う。
規約：path の全単体と元の Under 射を保持する。
使われ方：native roof prism の両端と 01 合成条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [Category.{u} I]

lemma coordinates_zero {n : ℕ} (Γ : Fin (n + 1) ⥤ I) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates Γ (OrderHom.const _ 0) i = nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i) ≫ SSet.ι₀ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    rfl

lemma coordinates_one_of_source {n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 1) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coordinates Γ t i = nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.underFunctor Γ i) ≫ SSet.ι₁ := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro P
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro k
    change t (((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i).app d P).down.toOrderHom k) = 1
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_apply]
    have h := t.monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum (P.obj k) i (P.obj k).left)
    rw [hi] at h
    exact le_antisymm (Fin.le_last _) h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
