module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientThickKernelEdges
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientLocalization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Saturation
/-!
概要：同じ実商の局所化を、新しい thick 核に cofiber を持つ辺の局所化へ移す。
方針：Ind が公開した反転飽和への一般補題と、新しい辺集合の同定を使う。
規約：既存の Verdier 辺・商関手を保持し、持ち上げた局所化そのものは明示入力に分ける。
使われ方：D-16 の Sp quotient 欄。追加宇宙での残る一般供給境界も型で明示する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]

lemma resolvedDGQuotientProjection_isThickLocalization (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P)).app
              (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_thickCofiberEdges_eq_invertedEdges]
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isLocalization R _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)).saturate

lemma resolvedDGQuotientFunctor_isThickLocalization (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P)).app
              (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_thickCofiberEdges_eq_invertedEdges]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isLocalization R D P).saturate

lemma resolvedDGQuotientFunctor_ulift_isThickLocalization_of_isLocalization (P : Set D)
    (W : Set (((SSet.uliftFunctor.{w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P)) W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            (((SSet.uliftFunctor.{w}).map
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges]
  exact hq.saturate

lemma resolvedDGQuotientProjection_ulift_isThickLocalization_of_isLocalization (P : Set D)
    (W : Set (((SSet.uliftFunctor.{w}).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGCategoryCellResolution.Source R D))) _⦋1⦌))
    (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)) W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            (((SSet.uliftFunctor.{w}).map
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges]
  exact hq.saturate

end SerrePositivity.InfinityCategories.Project.DerivedCategories
