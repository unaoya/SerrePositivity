module

public import SerrePositivity.KST.Spectra.D3CanonicalImageDoubleEndpointComparison

/-!
概要：パラメータ自然同型を全四角形の比較へ送り、同じ指定角値を厳密回収する。
方針：元の全順序・全入力 Hom の比較を同じ pairing へ前合成し、関手空間で curry する。
規約：角ごとに比較を選び直さない。使われ方：二方向実模型の単位終点の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
open EnrichedOrderedCylinder
local instance d3ParameterSquareComparisonCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
variable {D E : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}} (η : D ≅ E)

/-- 元のパラメータ自然同型から得る、全入力 Hom に自然な全四角形の同じ比較。 -/
def d3ParameterSquareIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3PointedKanParameterSquare E) (d3PointedKanParameterSquare D) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (((d3ParameterPreFunctorIso η).precomp d3PointedKanSquarePair).precomp
    (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom).curry rfl rfl

/-- 同じ全四角形比較の各角は、元の同じパラメータ成分による制限比較そのもの。 -/
lemma d3ParameterSquareIso_corner (i j : Fin 2) :
    HEq ((d3ParameterSquareIso η).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)))
      (d3PointedKanPreFunctorIso (η.hom.app (Opposite.op (i, j)))) := by
  unfold d3ParameterSquareIso
  refine (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq _ _ _ _).trans ?_
  refine (d3FunctorIso_curry_postcomp_evaluate _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorIso_precomp_precomp_heq _ _ _).trans ?_
  have hp : (lift (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j))
      (𝟙 PointedKanInfinity.{u}) ≫
      (β_ ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1]) PointedKanInfinity).hom) ≫
      d3PointedKanSquarePair =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (stageInclusion (C := PointedKanObject.{u}) (i, j)) := by
    change lift (𝟙 PointedKanInfinity)
      (SSet.const (stdSimplex.obj₀Equiv.symm i, stdSimplex.obj₀Equiv.symm j)) ≫
      d3PointedKanSquarePair = _
    exact d3PointedKanSquarePair_corner i j
  refine (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_heq_of_map_eq _ hp).trans ?_
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).symm.trans
    (heq_of_eq (d3ParameterPreFunctorIso_stage η (i, j)))

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
