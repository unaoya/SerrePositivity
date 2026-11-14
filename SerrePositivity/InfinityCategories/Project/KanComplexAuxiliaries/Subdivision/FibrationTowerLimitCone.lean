module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FibrationTower
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：整合族で定義した具体的な塔の極限を通常の極限錐として表す。
方針：隣接射での整合性から自然変換を作り、明示した lift と外延性を使う。
規約：極限の普遍性には Kan 性も fibration 性も不要。
使われ方：Goerss–Jardine VIII §1。写像空間の復元と具体的な塔の π の比較。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.FibrationTower
end SerrePositivity.KST.Spectra.FibrationTower
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.FibrationTower

variable (D : ℕᵒᵖ ⥤ SSet.{u})

/-- 具体的な整合族の極限を頂点とする錐。 -/
def sequentialCone : Cone D where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op)
  π := NatTrans.ofOpSequence
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ D.obj (op n))
      (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) n)
    (fun n ↦ by
      change 𝟙 _ ≫ _ = _
      rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp])

/-- 錐の射影は整合族の座標評価そのもの。 -/
lemma sequentialCone_π (n : ℕ) : (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone D).π.app (op n) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op) n := rfl

/-- 具体的な整合族の錐は通常の極限錐。 -/
def sequentialConeIsLimit : IsLimit (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone D) where
  lift s := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift _ _ (fun n ↦ s.π.app (op n)) (fun n ↦ s.w _)
  fac s n := by
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection _ _ _ _ n.unop
  uniq s m hm := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hom_ext (fun n ↦ D.obj (op n)) (fun n ↦ D.map (homOfLE (Nat.le_succ n)).op)
    intro n
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.lift_projection]
    exact hm (op n)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialCone := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialConeIsLimit := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialCone_π := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone_π

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialCone._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialCone._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialConeIsLimit._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialConeIsLimit._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.FibrationTower.sequentialConeIsLimit._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.sequentialConeIsLimit._proof_3
