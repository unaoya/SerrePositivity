module

public import SerrePositivity.InfinityCategories.F2.Ind.ElementsYonedaSliceValue
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconeIntervalPrism
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityCoconeTransformation

/-!
概要：元の Yoneda comma の pinched fiber 作用の区間表示を、元の native 密度変換へ厳密に同定する。
方針：同じ全余錐の uncurry、右 pinched 円筒の自然性、指定余錐の標準変換の円柱を順に使う。
規約：全 fiber パラメータと全高次の厳密な等式。
使われ方：同じ元の変換の unstraightening と指定値評価へ移す入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
abbrev presheafDensityFiberParameter : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x)
abbrev presheafDensityElementsParameter : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj (smallRightUnstraightening F)
abbrev presheafDensityFiberParameterInclusion :
    presheafDensityFiberParameter F x ⟶ presheafDensityElementsParameter F :=
  (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p x)
local notation "A" => presheafDensityFiberParameter F x
local notation "E" => presheafDensityElementsParameter F
local notation "i" => presheafDensityFiberParameterInclusion F x

/-- 元の同じ fiber へ制限した Yoneda 図式は、元の表現可能前層の定値図式そのもの。 -/
lemma presheafElementsYonedaDiagram_fiber :
    i ≫ presheafElementsYonedaDiagram F =
      SSet.const (functorVertex (representablePresheafInfinity x)) := by
  have hi : i ≫ (SSet.uliftFunctor.{u + 1, u}).map p = SSet.const (ULift.up x) := by
    rw [← Functor.map_comp, vertexFiberι_comp]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  rw [presheafElementsYonedaDiagram, ← Category.assoc, hi, SSet.const_comp,
    yonedaInfinityMap_vertex]

/-- 元の comma 比較の同じ pinched 作用を区間写像空間へ移す。 -/
def presheafElementsYonedaSliceInterval :
    A ⟶ intervalMappingSpace (functorVertex (representablePresheafInfinity x)) (functorVertex F) :=
  presheafElementsYonedaSliceMapping F x ≫ pinchedHomToIntervalMappingSpace _ _

/-- 元の区間表示全体は、元の密度余錐の標準変換を同じ fiber に制限した円柱そのもの。 -/
lemma presheafElementsYonedaSliceInterval_prism :
    intervalMappingUncurry (presheafElementsYonedaSliceInterval F x) =
      (Δ[1] ◁ i) ≫ (β_ Δ[1] E).hom ≫
        (simplicialHomotopyOfFunctorEdge
          (intervalMappingEdgeOfVertex (presheafDensityCoconeTransformationVertex F)).toTruncated).h := by
  rw [presheafElementsYonedaSliceInterval, pinchedHomToIntervalMappingSpace_uncurry]
  have hc := coconeTransformationPointAt_interval (presheafDensityCocone F) (functorVertex F)
    (presheafDensityCocone_vertex F)
  calc
    _ = rightMappingSpacePrism A ≫ joinMap i (𝟙 Δ[0]) ≫ (presheafDensityCocone F).val := by
      exact congrArg (fun q => rightMappingSpacePrism A ≫ q)
        (presheafElementsYonedaSliceMapping_uncurry F x)
    _ = (Δ[1] ◁ i) ≫ rightMappingSpacePrism E ≫ (presheafDensityCocone F).val := by
      simpa only [Category.assoc] using congrArg (fun q => q ≫ (presheafDensityCocone F).val)
        (rightMappingSpacePrism_naturality i).symm
    _ = _ := by
      simpa only [Category.assoc, presheafDensityCoconeTransformationVertex] using
        congrArg (fun q => (Δ[1] ◁ i) ≫ q) hc

end SerrePositivity.InfinityCategories.F2.Ind
