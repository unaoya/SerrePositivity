module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeFiberColimit
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityGlobalUniversal

/-!
概要：元の共同分類を右端に厳密に持つ一つの相対 join 図式と左 Kan 像は大域 Hom 普遍的。
方針：同じ図式の実際の全 fiber 余極限性を、同じ cocartesian 射影の大域普遍性へ渡す。
規約：元の左密度図式・右共同分類・全単位を保持。使われ方：strict 分類余錐の像の余極限性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
      (Opposite.op (SimplexCategory.mk 0)) v))
local notation "p" => weightedIndDensityIndexProjection F
local notation "H" => weightedIndDensityRelativeDiagram κ F hF

/-- 同じ相対 join 図式の左制限は、元の標準 weighted 密度図式そのもの。 -/
lemma weightedIndDensityRelativeDiagram_left_standard :
    relativeJoinInl p (𝟙 _) ≫ H = weightedIndDensityDiagram κ F :=
  (weightedIndDensityRelativeDiagram_left κ F hF).trans rfl

/-- 同じ共同分類を右端に厳密に持つ図式の全単位は、大域 Hom 普遍性を持つ。 -/
lemma weightedIndDensityRelativeDiagram_homUniversal :
    LeftKanHomUniversal p (F1B.kanRelativeJoinUnitLeft p H) :=
  weightedDensity_globalFamily_homUniversal F H
    (weightedIndDensityRelativeDiagram_allFibers_isColimit κ F hF)

/-- 元の同じ図式の左 Kan 像も、同じ全単位について大域 Hom 普遍性を持つ。 -/
lemma weightedIndDensityRelativeDiagram_image_homUniversal
    [∀ i, IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    LeftKanHomUniversal p (F1B.kanRelativeJoinUnitLeft p (H ≫ G)) :=
  weightedDensity_globalFamily_homUniversal F (H ≫ G)
    (weightedIndDensityRelativeDiagram_allFibers_image_isColimit κ F hF β hβ)

/-- 元の密度と元の共同分類を両端に厳密に持つ同じ一つの普遍族は、左 Kan 像も普遍的。 -/
lemma exists_weightedDensity_classifiedFamily_with_universal_KanImage
    [∀ i, IsKappaFiltered κ (F.obj i).val.left] {E : SSet.{u + 1}} [Quasicategory E]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ E} {G : IndInfinity κ C ⟶ E}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    ∃ H' : relativeJoin p (𝟙 _) ⟶ IndInfinity κ C,
      relativeJoinInl p (𝟙 _) ≫ H' = weightedIndDensityDiagram κ F ∧
      relativeJoinInr p (𝟙 _) ≫ H' = weightedIndClassification κ F hF ∧
      LeftKanHomUniversal p (F1B.kanRelativeJoinUnitLeft p H') ∧
      LeftKanHomUniversal p (F1B.kanRelativeJoinUnitLeft p (H' ≫ G)) :=
  ⟨H, weightedIndDensityRelativeDiagram_left_standard κ F hF,
    weightedIndDensityRelativeDiagram_right κ F hF,
    weightedIndDensityRelativeDiagram_homUniversal κ F hF,
    weightedIndDensityRelativeDiagram_image_homUniversal κ F hF β hβ⟩

end SerrePositivity.InfinityCategories.F2.Ind
