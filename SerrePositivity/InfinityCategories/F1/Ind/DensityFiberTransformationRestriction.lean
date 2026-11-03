module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingPostcompositionVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.HomotopyTransformationRestriction
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.HomotopyTransformationVertex
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafInfinity
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityConstruction
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1.Ind.ElementsYonedaSliceInterval

/-!
概要：元の密度変換空間を、同じ元の fiber 上の定値図式間の変換空間へ制限する。
方針：元の fiber 包含への前合成と、元の Yoneda 図式の定値性で両端を正規化する。
規約：変換空間の射として全高次で定義し、指定頂点の元のホモトピーも回収する。
使われ方：native 密度変換と元の大域変換の同型を、同じ fiber 上の全族へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "A" => presheafDensityFiberParameter F x
local notation "E" => presheafDensityElementsParameter F
local notation "i" => presheafDensityFiberParameterInclusion F x
local notation "T" => intervalMappingSpace (functorVertex (presheafElementsYonedaDiagram F))
  (functorVertex (SSet.const (functorVertex F) : E ⟶ PresheafInfinity C))

/-- 元の全密度変換を、同じ fiber 上の定値図式間の全変換へ制限する。 -/
def densityFiberTransformationRestriction : T ⟶
    intervalMappingSpace
      (functorVertex (SSet.const (functorVertex (representablePresheafInfinity x)) : A ⟶ _))
      (functorVertex (SSet.const (functorVertex F) : A ⟶ _)) :=
  intervalMappingPostOfEq ((pre i).app (PresheafInfinity C))
    (functorVertex (presheafElementsYonedaDiagram F))
    (functorVertex (SSet.const (functorVertex F) : E ⟶ _))
    (congrArg functorVertex (presheafElementsYonedaDiagram_fiber F x))
    (congrArg functorVertex (SSet.comp_const i (functorVertex F)))

/-- 指定変換の同じ円柱を、同じ fiber で制限した元のホモトピー。 -/
def densityFiberTransformationHomotopy (t : T _⦋0⦌) :
    SSet.Homotopy
      (SSet.const (functorVertex (representablePresheafInfinity x)) : A ⟶ PresheafInfinity C)
      (SSet.const (functorVertex F)) :=
  let H := functorHomotopyPrecomp
    (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated) i
  { h := H.h
    h₀ := H.h₀.trans (presheafElementsYonedaDiagram_fiber F x)
    h₁ := H.h₁.trans (SSet.comp_const i (functorVertex F))
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }

/-- 同じ制限射は、指定変換頂点を元の制限ホモトピーの指定頂点へ厳密に写す。 -/
lemma densityFiberTransformationRestriction_vertex (t : T _⦋0⦌) :
    (densityFiberTransformationRestriction F x).app (Opposite.op ⦋0⦌) t =
      homotopyTransformationVertex (densityFiberTransformationHomotopy F x t) := by
  have h := homotopyTransformationVertex_restriction
    (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated) i
    (presheafElementsYonedaDiagram_fiber F x) (SSet.comp_const i (functorVertex F))
    (densityFiberTransformationHomotopy F x t) rfl
  rw [homotopyTransformationVertex_recovered] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
