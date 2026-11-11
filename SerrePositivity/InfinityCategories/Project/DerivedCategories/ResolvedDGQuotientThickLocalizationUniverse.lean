module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientThickLocalization
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseAscent
/-!
概要：実商の thick 核局所化を任意の追加宇宙へ無条件に持ち上げる。
方針：同じ商の局所化を IsLocalization.ulift で持ち上げ、既存の反転辺同定で飽和する。
規約：既存の明示入力版を変更せず、quasicategory・ModelCategory 仮定を追加しない。
使われ方：D-16 の追加宇宙の quotient 欄。
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

lemma resolvedDGQuotientFunctor_ulift_isThickLocalization (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            (((SSet.uliftFunctor.{w}).map
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isLocalization R D P).ulift.saturate

lemma resolvedDGQuotientProjection_ulift_isThickLocalization (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P))
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
        {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
            (((SSet.uliftFunctor.{w}).map
              (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P))).app
                (Opposite.op ⦋0⦌) a) b)}) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges]
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isLocalization R _ _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)).ulift.saturate


end SerrePositivity.InfinityCategories.Project.DerivedCategories
