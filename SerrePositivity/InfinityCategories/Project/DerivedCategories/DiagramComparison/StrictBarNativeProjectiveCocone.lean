module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeProjectiveFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.SpecifiedProjectiveCocone
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion

/-!
概要：全 native 余錐族の射影的持ち上げは、各パラメーターで同じ余極限を与える。
方針：包含後の全余錐を元の native 余錐へ戻し、既存の余極限性を反映する。
規約：元の指定余錐を対象ごとに別の bar と取り替えない。
使われ方：3b-3 R6、同じ全余錐族を普遍余錐の全部分圏へ送る入力。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]
variable {C : Type (u + 1)} [Category.{u} C]
  (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1}))
  (hT : ∀ c j, moduleHomotopicallyProjective A PUnit.{1} ((T.obj c).obj j))

/-- U23の証明の分割：同じ全射影的余錐族の固定パラメーターでの射。 -/
def strictBarNativeProjectiveCoconeMapAt (c : C) :
    join ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶
        dgProjectiveModuleNerve A PUnit.{1} :=
  lift (SSet.const (ComposableArrows.mk₀ c))
    (𝟙 (join ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}))) ≫
    strictBarNativeProjectiveJoinFamily A J T hT

/-- 同じ全射影的余錐族を固定パラメーターで評価した余錐。 -/
def strictBarNativeProjectiveCoconeAt (c : C) :
    JoinCocone (joinInl ((SSet.uliftFunctor.{u + 1, u}).obj
      ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ≫
        strictBarNativeProjectiveCoconeMapAt A J T hT c) :=
  ⟨strictBarNativeProjectiveCoconeMapAt A J T hT c, rfl⟩

/-- 包含後の固定パラメーターの余錐は、元の同じ native 余錐全体に一致する。 -/
lemma strictBarNativeProjectiveCoconeAt_image (c : C) :
    (fullInclusionCocone A (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1})
      (strictBarNativeProjectiveCoconeAt A J T hT c)).val =
    (dgCoherentBarNormalizedNativeCoconeUnconditional A PUnit.{1}
      (smallStrictBarDiagram A (T.obj c))).val := by
  change strictBarNativeProjectiveCoconeMapAt A J T hT c ≫ _ = _
  unfold strictBarNativeProjectiveCoconeMapAt
  rw [Category.assoc, strictBarNativeProjectiveJoinFamily_image]
  exact strictBarNativeJoinFamilyAlong_atParameter A J T c

/-- 同じ全余錐族の固定パラメーターの余錐は、射影的模型の中でも余極限である。 -/
lemma strictBarNativeProjectiveCoconeAt_isColimit (c : C) :
    IsColimitCone (strictBarNativeProjectiveCoconeAt A J T hT c) := by
  apply isColimitCone_of_fullInclusion
  apply isColimitCone_of_initialBoundaryLifting_coconeRestriction
  rw [strictBarNativeProjectiveCoconeAt_image]
  exact (dgCoherentBarNormalizedNativeCoconeUnconditional_isColimit A PUnit.{1}
    (smallStrictBarDiagram A (T.obj c))).initialBoundaryLifting

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
