module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityGlobalFamily
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinUniversalHom

/-!
概要：weighted 密度の同じ大域図式とその左 Kan 像の、全添字上の Hom 普遍性。
方針：同じ cocartesian 射影の全 fiber の余極限性を大域的な指定単位へ渡す。
規約：右制限を頂点ごとの同型で置き換えない。使われ方：strict 分類との大域比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

variable {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
  (F : I ⥤ RightFibrationObject C)

/-- 全 fiber で余極限となる同じ全族の右制限は、指定単位について大域的に普遍。 -/
lemma weightedDensity_globalFamily_homUniversal {D : SSet.{u + 1}} [Quasicategory D]
    (H : relativeJoin ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F)))
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) ⟶ D)
    (hc : ∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v H)) :
    LeftKanHomUniversal _ (F1B.kanRelativeJoinUnitLeft _ H) := by
  have : CocartesianFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) :=
    uliftWeightedRightFibrationProjection_cocartesian F
  exact F1B.kanRelativeJoinUnitLeft_homUniversal _ H hc

/-- 元の全族とその指定左 Kan 像は、一つの同じ全族のまま大域的 Hom 普遍性を持つ。 -/
lemma exists_weightedDensity_globalFamily_with_universal_KanImage
    (κ : Cardinal.{u}) {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I]
    (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    ∃ H : relativeJoin ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (rightFibrationTotalDiagram F)))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) ⟶ IndInfinity κ C,
      relativeJoinInl _ _ ≫ H = weightedIndDensityDiagram κ F ∧
        LeftKanHomUniversal _ (F1B.kanRelativeJoinUnitLeft _ H) ∧
        LeftKanHomUniversal _ (F1B.kanRelativeJoinUnitLeft _ (H ≫ G)) := by
  obtain ⟨H, hH, hc, hGc⟩ := exists_weightedDensity_globalFamily_with_KanImage κ F β hβ
  exact ⟨H, hH, weightedDensity_globalFamily_homUniversal F H hc,
    weightedDensity_globalFamily_homUniversal F (H ≫ G) hGc⟩

end SerrePositivity.InfinityCategories.F2.Ind
