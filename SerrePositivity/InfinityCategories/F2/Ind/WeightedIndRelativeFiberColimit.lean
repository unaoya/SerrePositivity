module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeFiberCoefficientColimit
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityRelativeFamilyImage

/-!
概要：元の全単位を実現した同じ相対 join 図式と左 Kan 像は、実際の全 fiber 余錐で余極限。
方針：元の係数同型での余極限性の検出と、同じ全余錐の像・図式の等式による移送を使う。
規約：元の全図式と実際の fiber 余錐を固定。使われ方：指定全単位の大域 Hom 普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op ⦋0⦌) v))
local notation "p" => weightedIndDensityIndexProjection F
local notation "H" => weightedIndDensityRelativeDiagram κ F hF

/-- 元の相対 join 図式の実際の各係数 fiber 余錐は、元の同じ図式の余極限。 -/
lemma weightedIndDensityRelativeDiagram_fiber_isColimit (i : I) :
    IsColimitCone (F1B.kanRelativeJoinFiberCocone p (ULift.up (nerveVertex i)) H) := by
  let c := F1B.kanRelativeJoinFiberCocone p (ULift.up (nerveVertex i)) H
  let e := weightedIndCoefficientFiberIso F i
  let T := vertexFiberι p (ULift.up (nerveVertex i)) ≫ relativeJoinInl p (𝟙 _) ≫ H
  have := sliceUnderRestrict_trivialKanFibration_of_precompositionEquivalence T e.hom
    (isPrecompositionEquivalence_of_iso e)
  apply ((qCatEquivalenceOfTrivialKanFibration (sliceUnderRestrict T e.hom)).isInitialVertex_iff c).mpr
  exact (coherentCoconeOfDiagramEq_isColimit_iff
    (weightedIndRelativeFiberCoefficient_diagram κ F hF i) (c.restrict e.hom)).mpr
      (weightedIndRelativeFiberCoefficientCocone_isColimit κ F hF i)

/-- 同じ相対 join 図式は、元の底の全頂点における実際の fiber 余錐で余極限となる。 -/
lemma weightedIndDensityRelativeDiagram_allFibers_isColimit
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    IsColimitCone (F1B.kanRelativeJoinFiberCocone p v H) := by
  obtain ⟨v⟩ := v
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  exact weightedIndDensityRelativeDiagram_fiber_isColimit κ F hF i

/-- 元の同じ全図式の左 Kan 像も、元の全頂点の実際の fiber 余錐で余極限となる。 -/
lemma weightedIndDensityRelativeDiagram_allFibers_image_isColimit
    [∀ i, IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    (v : ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) _⦋0⦌) :
    IsColimitCone (F1B.kanRelativeJoinFiberCocone p v (H ≫ G)) := by
  obtain ⟨v⟩ := v
  obtain ⟨i, rfl⟩ := nerveEquiv.symm.surjective v
  let c := F1B.kanRelativeJoinFiberCocone p (ULift.up (nerveVertex i)) H
  let e := weightedIndCoefficientFiberIso F i
  have hGd := weightedIndRelativeFiberCoefficientCocone_image_isColimit κ F hF i β hβ
  have hGc : IsColimitCone (mapJoinCocone G c) := by
    apply (mapJoinCocone_isColimit_iff_restrict G e.hom (isPrecompositionEquivalence_of_iso e) c).mpr
    exact (mapJoinCocone_diagramEq_isColimit_iff G
      (weightedIndRelativeFiberCoefficient_diagram κ F hF i) (c.restrict e.hom)).mp hGd
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hGc
  exact kanRelativeJoinFiberCocone_post_val p (ULift.up (nerveVertex i)) H G

end SerrePositivity.InfinityCategories.F2.Ind
