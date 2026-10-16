module
public import SerrePositivity.DifferentialGraded.Perfect.SmallStageCover
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Derived.ResolutionHom
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-! # 主導来圏内のPerfの本質的小性

小さい有限cell代表族の関手像とretract閉包を使う。全加群圏や導来圏の対象型をsmallとはしない。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 有限cellの小さい段階別代表が全finite cellを同型まで被覆する。 -/
instance moduleFiniteCellOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (moduleFiniteCellOver A D S) where
  exists_small_le' := by
    refine ⟨ObjectProperty.ofObj (moduleFiniteCellStageObject A D S), inferInstance, ?_⟩
    intro M hM
    obtain ⟨i, ⟨e⟩⟩ := moduleFiniteCellOver_exists_stage A D hM
    exact ⟨_, ⟨i⟩, ⟨e.symm⟩⟩

/-- finite cellの主導来像は、固定版Mathlibの関手像の定理により本質的にu-small。 -/
instance derivedFiniteCellOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (derivedFiniteCellOver A D S) := by
  dsimp [derivedFiniteCellOver]
  infer_instance

/-- 主導来圏の局所小性とretract閉包の一般定理からPerfの本質的小性を得る。 -/
instance modulePerfectOverEssentiallySmall (S : Set D) :
    ObjectProperty.EssentiallySmall.{u} (modulePerfectOver A D S) := by
  dsimp [modulePerfectOver]
  infer_instance

/-- Perfの充満部分圏はu-smallな圏と同値である。対象型そのもののsmall性とは区別する。 -/
instance perfectModuleCategoryOverEssentiallySmall (S : Set D) :
    EssentiallySmall.{u} (PerfectModuleCategoryOver A D S) := inferInstance

/-- 実際の主導来対象からなる小さい代表部分族を、Perf内に選択できる。 -/
lemma modulePerfectOver_exists_small_representatives (S : Set D) :
    ∃ (P : ObjectProperty (DerivedModuleCategory A D)) (_ : ObjectProperty.Small.{u} P),
      P ≤ modulePerfectOver A D S ∧ modulePerfectOver A D S ≤ P.isoClosure :=
  ObjectProperty.EssentiallySmall.exists_small_le (modulePerfectOver A D S)

end SerrePositivity.DifferentialGraded
