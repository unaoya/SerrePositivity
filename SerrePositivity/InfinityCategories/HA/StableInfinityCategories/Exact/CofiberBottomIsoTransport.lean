module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.SpecifiedHomotopyLift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExactFunctorChoice
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.TrivialFibrationStability
/-!
概要：cofiber 四角形の底辺の全関手同型を、cofiber 四角形全体の実同型へ延長する。
方針：指定底辺の可逆ホモトピーを単射に沿って延長し、同じ底辺の cofiber 比較を使う。
規約：零頂点と実押し出し性を保持。使われ方：Verdier 分数表示による完全性の反映。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
/-- 底辺が全関手圏で同型な二つの実 cofiber 四角形は、四角形全体として同型。 -/
lemma nonempty_cofiberSquareFunctorIso_of_bottom_iso {X : SSet.{u}} [Quasicategory X]
    (s t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (hs : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence s) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ s.square) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square t.square) := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy e.symm
  have hH : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H a).toTruncated := by
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e.symm) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e.symm) a
  obtain ⟨w, G, hw, _, hG⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.exists_mono_homotopy_lift_target _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square) s.square H hH
  let ew : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso w s.square := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy G hG
  let corner := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 1
  have ez : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex w 0 1) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex s.square 0 1) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map ew (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) corner)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at h
    exact h
  let d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X := {
    square := w
    zero_corner := s.zero_corner.of_vertexIso ez.symm }
  have hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d := hs.of_functorIso ew.symm
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square))
  let r : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f := {
    toZeroTriangle := d
    bottom_edge := hw.trans (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := hd }
  let v : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare f := {
    toZeroTriangle := t
    bottom_edge := (SSet.yonedaEquiv.symm_apply_apply _).symm
    isPushout := ht }
  obtain ⟨ev⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberSquareFunctorIso r v
  exact ⟨ew.symm ≪≫ ev⟩
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
