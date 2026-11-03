module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Ind.CanonicalIntervalYonedaValue
public import SerrePositivity.InfinityCategories.F1.Ind.DensityCanonicalTransportEquivalence
public import SerrePositivity.InfinityCategories.F1.Ind.DensityCanonicalValueCriterion
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceComparison
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval
public import SerrePositivity.InfinityCategories.HomotopyLimits.Ind.ElementsYonedaSliceValue
public import SerrePositivity.InfinityCategories.F1.Ind.YonedaSlice

/-!
概要：元の小さい元の圏から Yoneda comma への元の密度比較自体が同値。
方針：同じ全 fiber の canonical 輸送同値を、元の指定値写像と right fibration の判定へ戻す。
規約：元の比較と元の余錐を保持し、同値性を仮定しない。
使われ方：Ind の元の小さい κ-filtered 表示を Yoneda comma の模型へ移す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 元の comma 比較の実際の全 fiber 値写像自身が同値。 -/
lemma presheafElementsYonedaSliceValue_isQCatEquivalence (x : C _⦋0⦌) :
    IsQCatEquivalence (presheafElementsYonedaSliceValue F x) :=
  (presheafElementsYonedaSliceValue_iff_canonicalTransport F x).mpr
    (presheafDensityCanonicalTransportValue_isQCatEquivalence F x)

/-- 元の小さい元の圏から同じ元の前層への Yoneda comma の密度比較自体が同値。 -/
lemma presheafElementsYonedaSliceComparison_isQCatEquivalence :
    IsQCatEquivalence (presheafElementsYonedaSliceComparison F) :=
  presheafElementsYonedaSliceComparison_isQCatEquivalence_of_values F
    (presheafElementsYonedaSliceValue_isQCatEquivalence F)

end SerrePositivity.InfinityCategories.F2.Ind
