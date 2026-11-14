module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNativeParameterRecovery
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ProjectiveBarNativeCocone

/-!
概要：射影的な値を持つ strict 図式の全 native 余錐族を同じ射影的模型へ持ち上げる。
方針：元の同じ余錐への固定パラメーター比較と、既存 bar の射影性を用いる。
規約：全高次単体と元の余錐を保つ包含の右逆である。
使われ方：3b-3 R6、全余錐族と D(A) への既存の比較との接続。
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
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 射影的な値を持つ元の strict 図式の同じ正規化 bar も射影的である。 -/
lemma strictBarNormalizedFunctor_projective (F : J ⥤ ModuleCategory A PUnit.{1})
    (hF : ∀ j, moduleHomotopicallyProjective A PUnit.{1} (F.obj j)) :
    moduleHomotopicallyProjective A PUnit.{1} ((strictBarNormalizedFunctor A J).obj F) := by
  apply dgCoherentBarNormalizedModule_homotopicallyProjective
  intro s
  exact hF (s.down.obj 0)

variable {C : Type (u + 1)} [Category.{u} C]
  (T : C ⥤ (J ⥤ ModuleCategory A PUnit.{1}))
  (hT : ∀ c j, moduleHomotopicallyProjective A PUnit.{1} ((T.obj c).obj j))

/-- 同じ全パラメーターの native 余錐族を、元の図式族に沿って引き戻す。 -/
def strictBarNativeJoinFamilyAlong :
    nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ dgNerve A (RightModule A PUnit.{1}) :=
  (nerveMap T ▷ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) ≫ strictBarNativeJoinFamily A J

/-- U20の前提計算：パラメーター関手に沿う制限は同じ元のnative余錐を保つ。 -/
lemma strictBarNativeJoinFamilyAlong_atParameter (c : C) :
    lift (SSet.const (ComposableArrows.mk₀ c))
        (𝟙 (join ((SSet.uliftFunctor.{u + 1, u}).obj
          ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}))) ≫
      strictBarNativeJoinFamilyAlong A J T =
    (dgCoherentBarNormalizedNativeCoconeUnconditional A PUnit.{1}
      (smallStrictBarDiagram A (T.obj c))).val := by
  unfold strictBarNativeJoinFamilyAlong
  rw [← Category.assoc, lift_whiskerRight, SSet.const_comp, nerveMap_app_mk₀]
  have h := strictFamilyCurry_evaluateAt A (RightModule A PUnit.{1})
    (strictBarNativeJoinFamily A J) (T.obj c)
  change curry (uncurry (strictBarNativeFunctorCocone A J).val) ≫ _ = _ at h
  rw [curry_uncurry] at h
  exact h.symm.trans (strictBarNativeFunctorCocone_atParameter A J (T.obj c))

include hT in
/-- 全余錐族の全頂点における射影性を、同じ元の指定余錐から導く。 -/
lemma strictBarNativeJoinFamilyAlong_projective :
    ∀ z : (nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1})) _⦋0⦌,
      dgModuleProjectiveProperty A PUnit.{1}
        (((strictBarNativeJoinFamilyAlong A J T).app _ z).obj 0) := by
  rintro ⟨d, z⟩
  obtain ⟨c, rfl⟩ := ComposableArrows.mk₀_surjective d
  have he := congrArg (fun f => (f.app (Opposite.op ⦋0⦌) z).obj 0)
    (strictBarNativeJoinFamilyAlong_atParameter A J T c)
  change ((strictBarNativeJoinFamilyAlong A J T).app
      (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ c, z)).obj 0 =
    ((dgCoherentBarNormalizedNativeCoconeUnconditional A PUnit.{1}
      (smallStrictBarDiagram A (T.obj c))).val.app (Opposite.op ⦋0⦌) z).obj 0 at he
  rw [he]
  apply dgBarCocone_vertices A PUnit.{1} _ _ _ z
  · intro s
    exact hT c (s.down.down.obj 0)
  · rw [dgCoherentBarNormalizedNativeCocone_vertex]
    exact strictBarNormalizedFunctor_projective A J (T.obj c) (hT c)

/-- 同じ全 native 余錐族の、射影的充満部分圏への全単体的持ち上げ。 -/
def strictBarNativeProjectiveJoinFamily :
    nerve C ⊗ join ((SSet.uliftFunctor.{u + 1, u}).obj ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) (Δ[0] : SSet.{u + 1}) ⟶ dgProjectiveModuleNerve A PUnit.{1} :=
  fullInclusionLift A (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1})
    (strictBarNativeJoinFamilyAlong A J T) (strictBarNativeJoinFamilyAlong_projective A J T hT)

/-- 包含で戻すと、元の同じ全 native 余錐族に厳密に一致する。 -/
lemma strictBarNativeProjectiveJoinFamily_image :
    strictBarNativeProjectiveJoinFamily A J T hT ≫
        SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
          (dgFullSubcategoryInclusion A (RightModule A PUnit.{1})
            (dgModuleProjectiveProperty A PUnit.{1})) =
      strictBarNativeJoinFamilyAlong A J T :=
  fullInclusionLift_comp A (RightModule A PUnit.{1}) (dgModuleProjectiveProperty A PUnit.{1}) _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
