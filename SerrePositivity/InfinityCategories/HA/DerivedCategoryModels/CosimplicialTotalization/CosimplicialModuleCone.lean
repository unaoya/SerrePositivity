module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteTotApexTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorPointwiseLimitExistence

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 全交代余面関手を指定頂点とする、一つの全関手圏錐。 -/
def discreteCochainFunctorCone : JoinCone (rawDiscreteTotFunctorDiagram A) :=
  Classical.choose (exists_discreteCochainFunctorCone A)

theorem discreteCochainFunctorCone_isLimit : IsLimitCone (discreteCochainFunctorCone A) :=
  (Classical.choose_spec (exists_discreteCochainFunctorCone A)).1

theorem discreteCochainFunctorCone_vertex :
    (discreteCochainFunctorCone A).vertex =
      functorVertex (nerveMap (discreteCochainFunctor A) ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  (Classical.choose_spec (exists_discreteCochainFunctorCone A)).2

/-- 元の全離散評価図式を固定した、点評価図式の同じ値。 -/
theorem rawDiscreteTotFunctorDiagram_at (M : CosimplicialObject (ModuleCat.{u} A)) :
    evaluateFunctorDiagram (rawDiscreteTotFunctorDiagram A) (ComposableArrows.mk₀ M) =
      strictCosimplicialModuleNerve A M ≫ discreteModuleSource A := by
  have h := congrArg (fun f => joinInr (Δ[0] : SSet.{u+1})
    ((SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory)) ≫ f)
      (rawDiscreteTotFunctorCone_at A M)
  exact (evaluateFunctorCone (rawDiscreteTotFunctorCone A)
    (ComposableArrows.mk₀ M)).property.symm.trans (h.trans (rawCosimplicialModuleCone A M).property)

/-- 同じ一つの全関手圏錐は、全ての離散入力で極限錐になる。 -/
theorem discreteCochainFunctorCone_isPointwise :
    IsPointwiseLimitCone (discreteCochainFunctorCone A) := by
  have hr : IsPointwiseLimitCone (rawDiscreteTotFunctorCone A) := by
    intro M
    obtain ⟨M, rfl⟩ := ComposableArrows.mk₀_surjective M
    exact (isLimitCone_iff_of_cone_val_eq _ _ (rawDiscreteTotFunctorCone_at A M)).2
      (rawCosimplicialModuleCone_isLimit A M)
  exact isPointwiseLimitCone_of_isLimitCone_of_hasPointwiseLimits hr.hasPointwiseLimits
    (discreteCochainFunctorCone A) (discreteCochainFunctorCone_isLimit A)

/-- D05：同じ元の離散図式を底とし、交代余面複体を頂点とする指定錐。 -/
def cosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A) :=
  joinConeOfDiagramEq (rawDiscreteTotFunctorDiagram_at A M)
    (evaluateFunctorCone (discreteCochainFunctorCone A) (ComposableArrows.mk₀ M))

theorem cosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (cosimplicialModuleCone A M) :=
  joinConeOfDiagramEq_isLimit _ _
    (discreteCochainFunctorCone_isPointwise A (ComposableArrows.mk₀ M))

/-- D06：同じ錐の頂点は整数次数へ零延長した同じ交代余面複体の像。 -/
theorem cosimplicialModuleCone_vertex (M : CosimplicialObject (ModuleCat.{u} A)) :
    (cosimplicialModuleCone A M).vertex =
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (nerveVertex ((discreteCochainFunctor A).obj M)) := by
  rw [JoinCone.vertex_eq, cosimplicialModuleCone, joinConeOfDiagramEq_val]
  change (evaluateFunctorCone (discreteCochainFunctorCone A)
    (ComposableArrows.mk₀ M)).vertex = _
  rw [evaluateFunctorCone_vertex, discreteCochainFunctorCone_vertex,
    evaluateFunctorAt_functorVertex]
  change (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
    ((nerveMap (discreteCochainFunctor A)).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ M)) = _
  rw [nerveMap_app_mk₀]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
