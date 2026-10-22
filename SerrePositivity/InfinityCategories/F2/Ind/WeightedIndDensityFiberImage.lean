module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityFiber
public import SerrePositivity.InfinityCategories.F2.Ind.RightClassifiedIndDensityImage

/-!
概要：weighted 密度図式の各 fiber の指定 native 余極限余錐は、左 Kan 延長で保存される。
方針：同じ fiber 同型で元の密度余錐へ移し、全余錐の一意性と形状制限の同値で戻す。
規約：余錐を指定でき、対象ごとの頂点同型で代用しない。使われ方：全相対 join 図式の像の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]
  {D : SSet.{u + 1}} [Quasicategory D]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
  (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
  (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
include β hβ

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 同じ weighted fiber の任意の指定余極限余錐の像は、元の左 Kan 延長で余極限となる。 -/
lemma weightedIndDensityFiber_image_isColimit (i : I)
    (c : JoinCocone (vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) (ULift.up (nerveVertex i)) ≫
        weightedIndDensityDiagram κ F)) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone G c) := by
  let e := uliftWeightedNerveFiberIso.{u, u + 1} (rightFibrationTotalDiagram F) i
  let d := coherentCoconeOfDiagramEq (weightedIndDensityFiber_diagram κ F i).symm
    (rightClassifiedIndDensityCocone κ (F.obj i))
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (rightClassifiedIndDensityCocone_isColimit κ (F.obj i))
  have hGd : IsColimitCone (mapJoinCocone G d) :=
    (mapJoinCocone_diagramEq_isColimit_iff G _ _).mpr
      (rightClassifiedIndDensity_image_isColimit κ β hβ (F.obj i))
  let T := vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveProjection (rightFibrationTotalDiagram F))) (ULift.up (nerveVertex i)) ≫
      weightedIndDensityDiagram κ F
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence T e.hom
    (isPrecompositionEquivalence_of_iso e)
  have hr : IsColimitCone (c.restrict e.hom) :=
    ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict T e.hom)).isInitialVertex_iff c).mp hc
  apply (mapJoinCocone_isColimit_iff_restrict G e.hom (isPrecompositionEquivalence_of_iso e) c).mpr
  exact hGd.of_functorIso
    ((coconeFunctorIsoOfVertexIso d (c.restrict e.hom)
      (colimitConeIso d (c.restrict e.hom) hd hr)).postcomp G)

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 全添字の各 fiber 上で、元の指定余極限余錐は左 Kan 延長によって保存される。 -/
lemma weightedIndDensity_allFibers_image_isColimit
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌)
    (c : JoinCocone (vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) v ≫ weightedIndDensityDiagram κ F))
    (hc : IsColimitCone c) : IsColimitCone (mapJoinCocone G c) := by
  obtain ⟨v⟩ := v
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  exact weightedIndDensityFiber_image_isColimit κ F β hβ i c hc

end SerrePositivity.InfinityCategories.F2.Ind
