module

public import SerrePositivity.KST.Spectra.CoherentPathParameters

/-!
概要：二単体の path の区間パラメーターは、既存の最大内点座標で元の区間に戻る。
方針：一つの内点を含むかどうかで最大元を 0・1 と計算する。
規約：包含の向きを保持。使われ方：Hom の比較二単体から元の Hom の辺を取り出す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.CoherentPathCoordinates

/-- 一つの内点のフラグは、元の path の最大内点座標そのもの。 -/
lemma triangleFlaggedPath_maximum (a : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (i := (0 : Fin 2)) (flaggedPath.{u} (fun _ : Fin 1 ↦ a)) = a := by
  fin_cases a
  · let k := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (i := (0 : Fin 2)) (flaggedPath.{u} (fun _ : Fin 1 ↦ 0))
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum_mem (i := (0 : Fin 2))
      (flaggedPath.{u} (fun _ : Fin 1 ↦ 0))
    change k.castSucc = 0 ∨ k.castSucc = Fin.last 2 ∨
      ∃ r : Fin 1, k.castSucc = r.succ.castSucc ∧ (0 : Fin 2) = 1 at hm
    have hk := k.isLt
    apply Fin.ext
    change k.val = 0
    rcases hm with h | h | ⟨_, _, h⟩
    · have hv := congrArg Fin.val h
      exact hv
    · have hv := congrArg Fin.val h
      change k.val = 2 at hv
      omega
    · exact (by decide : (0 : Fin 2) ≠ 1) h |>.elim
  · apply le_antisymm (Fin.le_last _) ?_
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.le_pathLastMaximum
    exact Or.inr (Or.inr ⟨0, rfl, rfl⟩)

/-- 元の path の区間パラメーターに最大内点座標を続けると、区間の恒等射。 -/
lemma trianglePathInterval_maximum :
    trianglePathInterval.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (0 : Fin 2) = 𝟙 (Δ[1] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply SSet.stdSimplex.ext
  intro i
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (i := (0 : Fin 2)) (flaggedPath (fun _ : Fin 1 ↦ a i)) = a i
  exact triangleFlaggedPath_maximum _

end SerrePositivity.KST.Spectra.CoherentPathCoordinates
