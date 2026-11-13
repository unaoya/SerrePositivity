module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.ResolvedDGQuotientThickKernelSource
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseKernelEdges
/-!
概要：同じ実平坦商が反転する辺は、新しい thick 核に cofiber を持つ辺と一致する。
方針：平坦源と元の源の零対象反映を、完全関手の核の一般辺判定へ渡す。
規約：旧 Verdier 辺との無条件等式は主張せず、局所化の飽和移行は別に行う。
使われ方：D-16 の Sp quotient 欄の反転飽和、任意の追加 ULift 宇宙版。
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

lemma resolvedDGQuotientProjection_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {b | ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b)} = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges_eq_invertedEdges_of_kernel (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientFunctor_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {b | ∃ a : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P)) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P)).app
            (Opposite.op ⦋0⦌) a) b)} = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor R D P
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges_eq_invertedEdges_of_kernel (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P) _
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientProjection_ulift_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (((SSet.uliftFunctor.{w}).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b)} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R (DGCategoryCellResolution.Source R D)
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P) :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_localKFlat R D P)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges_ulift_essentialImage_eq_invertedEdges
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection R D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientProjection_zero_iff_thickEssentialImage R D P)

lemma resolvedDGQuotientFunctor_ulift_thickCofiberEdges_eq_invertedEdges (P : Set D) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {b | ∃ a : ((SSet.uliftFunctor.{w}).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R D P))) _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
          (((SSet.uliftFunctor.{w}).map
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P))).app
              (Opposite.op ⦋0⦌) a) b)} =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges ((SSet.uliftFunctor.{w}).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P)) := by
  let := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Pretriangulated.dgNerve_isStable_of_pretriangulated R D
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R D P
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor R D P
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges_ulift_essentialImage_eq_invertedEdges
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickKernelInclusion R D P))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R D P)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_zero_iff_thickEssentialImage R D P)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
