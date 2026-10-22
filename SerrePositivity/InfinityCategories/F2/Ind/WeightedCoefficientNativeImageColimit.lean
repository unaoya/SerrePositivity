module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeColimit
public import SerrePositivity.InfinityCategories.F2.Ind.RightClassifiedIndDensityImage

/-!
概要：同じ全 weighted 密度変換の指定 native 係数余錐の像も、元の左 Kan 延長で余極限。
方針：同じ係数図式上の元の分類密度余錐との全余錐同型を、元の延長で写す。
規約：元の指定係数余錐を保持し、一般の保存性を仮定しない。使われ方：全変換の像の局所普遍性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v)) (i : I) [IsKappaFiltered κ (F.obj i).val.left]
  {D : SSet.{u + 1}} [Quasicategory D]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}

/-- 元の全変換の同じ指定係数余錐の像は、元の左 Kan 延長によって余極限となる。 -/
lemma weightedIndDensityCoefficientCocone_image_isColimit
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    IsColimitCone (mapJoinCocone G (weightedIndDensityCoefficientCocone κ F hF i)) := by
  let c := rightClassifiedIndDensityCocone κ (F.obj i)
  let d := weightedIndDensityCoefficientCocone κ F hF i
  have hc : IsColimitCone c := rightClassifiedIndDensityCocone_isColimit κ (F.obj i)
  have hd : IsColimitCone d := weightedIndDensityCoefficientCocone_isColimit κ F hF i
  have hGc : IsColimitCone (mapJoinCocone G c) :=
    rightClassifiedIndDensity_image_isColimit κ β hβ (F.obj i)
  exact hGc.of_functorIso
    ((coconeFunctorIsoOfVertexIso c d (colimitConeIso c d hc hd)).postcomp G)

end SerrePositivity.InfinityCategories.F2.Ind
