module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionKanComparison
public import SerrePositivity.KST.SConstruction.StrictSimplicialTransformationComponent
public import SerrePositivity.KST.SConstruction.OneDirectionWeakComparison
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinityLocalization

/-! # 元の S₁ 比較の全基点同型と関手 ∞ 圏での可逆性
概要：同じ Ex∞ 比較の全基点 π 同型と、全入力上の実際の関手同型を得る。
方針：元の商比較の局所化可逆性を Ex∞ で保存し、点つき Whitehead と γ1 に移す。
規約：豊穣自然な厳密逆を選んだとは主張しない。使われ方：BF 構造射の源の span。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.SimplicialModel
variable (A : Type u) [CommRing A]

/-- 元の同じ S₁ 商比較の Ex∞ 像は全基点・全次数で π 同型。 -/
lemma presentedPerfectDGOneDirectionKanComparisonMap_piIsomorphism (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (presentedPerfectDGOneDirectionKanComparisonMap A r C).hom.right := by
  apply kanPiIsomorphism_of_localized_isIso
  change IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
    (oneDirectionReducedComparison r
      (stableCategoryModel (presentedPerfectDGStableCategory A C))).right))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
    (oneDirectionReducedComparison_localized_isIso r
      (stableCategoryModel (presentedPerfectDGStableCategory A C)))

/-- γ1 へ渡した比較成分は、同じ元の S₁ 商比較の Ex∞ 像そのもの。 -/
lemma presentedPerfectDGOneDirectionKanComparison_componentHom (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    Spectra.StrictEnrichedTransformation.componentHom _ _
      (presentedPerfectDGOneDirectionKanComparison A r) C =
      presentedPerfectDGOneDirectionKanComparisonMap A r C :=
  strictSimplicialTransformation_componentHom _ _ _ C _
    (presentedPerfectDGOneDirectionKanComparison_app A r C)

/-- 同じ元の Kan 比較の coherent な辺は可逆。 -/
lemma presentedPerfectDGOneDirectionKanComparison_edge_isInvertible (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
      (presentedPerfectDGOneDirectionKanComparisonMap A r C)) :=
  pointedKanObject_edge_isInvertible_of_piIsomorphism _
    (presentedPerfectDGOneDirectionKanComparisonMap_piIsomorphism A r C)

/-- 元の S₁ 比較による、全 native 入力上の実際の PointedKanInfinity 値関手同型。 -/
def presentedPerfectDGOneDirectionKanComparisonFunctorIso (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (presentedPerfectDGOneDirectionKanInfinityFunctor A r)
      (presentedPerfectDGBoundaryKanInfinityFunctor A r) :=
  Spectra.StrictEnrichedTransformation.functorIso _ _
    (presentedPerfectDGOneDirectionKanComparison A r) (by
      intro C
      rw [presentedPerfectDGOneDirectionKanComparison_componentHom]
      exact presentedPerfectDGOneDirectionKanComparison_edge_isInvertible A r C)

end SerrePositivity.KST.SConstruction
