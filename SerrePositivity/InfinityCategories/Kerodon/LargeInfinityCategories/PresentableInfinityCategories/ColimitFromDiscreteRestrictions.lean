module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoproductRealizationColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ElementsCoproductKanProjection

/-!
概要：指定図式の離散制限の小余積と幾何学的実現から元の余極限を構成する。
方針：全単体への展開の各次数だけに小余積の存在を要求する。
規約：標的全体の小余積存在を入力にしない。
使われ方：表現可能図式の余極限から P_Σ 専用反映を構成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
attribute [local instance] CategoryTheory.uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：同じ図式の全離散制限の小余積と幾何学的実現から余極限が存在する。
方針：各 bar 次数の全射影を指定離散制限として読み、実現を元の図式へ戻す。
規約：元の任意の小さい形状を保持する。
使われ方：特定の表現可能図式だけの余極限の構成。 -/
lemma hasColimit_of_discreteRestrictions_geometricRealizations
    {X : SSet.{u + 1}} [Quasicategory X] {K : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X)
    (hcop : ∀ (I : Type u) (f : nerve (Discrete I) ⟶ K),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((SSet.uliftFunctor.{u + 1, u}).map f ≫ F))
    (hgeom : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.HasSmallGeometricRealizations X) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F := by
  let Y := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialBarSimplexFamily K
  let j := (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap K)
  let e := (SSet.uliftFunctor.{u + 1, u}).mapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialBarIndexNerveIso K)
  let F' := e.hom ≫ (j ≫ F)
  have hlocal := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elements_leftKanDiagram_hasColimit_of_fibers Y F' (fun i ↦ by
    simpa only [F', e, j, Functor.mapIso_hom, Functor.map_comp, Category.assoc] using
      hcop (Y.obj i) (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.elementsDegreeFiber Y i ⋙ CostructuredArrow.proj _ i) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.simplicialBarIndexNerveIso K).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap K))
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit F' := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_localLeftKan_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (Functor.Elements.π Y))) F' hlocal hgeom
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre j).app X) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localization_pre_isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} K) X
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre e.hom).app X) :=
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e) X).isFullyFaithful
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_fullyFaithfulPrecomposition j hj F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.hasColimit_of_fullyFaithfulPrecomposition e.hom he (j ≫ F) hx)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
