module
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.OppositeWeakHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
概要：元のop反転は、元の射自身の弱ホモトピー同値性も反映する。
方針：既存の保存則を二度適用し、同じop自己同値の単位で元の射へ戻す。
規約：始域・終域のKan性を仮定しない。元の射を別の比較射へ置き換えない。
使われ方：反対要素圏で元のnative fiber射の弱同値性を検査する係数移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 同じop自己同値の単位で、既存の弱同値保存則を元の射へ反映する。 -/
theorem opposite_map_isWeakHomotopyEquivalence_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    IsWeakHomotopyEquivalence (SSet.opFunctor.map f) ↔ IsWeakHomotopyEquivalence f := by
  constructor
  · intro hf
    have hff := SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence
      (SSet.opFunctor.map f) hf
    have hx := (isPrecompositionEquivalence_of_iso (SSet.opEquivalence.unitIso.app X)).isWeakHomotopyEquivalence
    have hy := (isPrecompositionEquivalence_of_iso (SSet.opEquivalence.unitIso.app Y)).isWeakHomotopyEquivalence
    simp only [Iso.app_hom] at hx hy
    have hn : f ≫ SSet.opEquivalence.unitIso.hom.app Y =
        SSet.opEquivalence.unitIso.hom.app X ≫ SSet.opFunctor.map (SSet.opFunctor.map f) :=
      SSet.opEquivalence.unitIso.hom.naturality f
    apply hy.cancel_right
    rw [hn]
    exact hx.comp hff
  · exact SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence f
end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
