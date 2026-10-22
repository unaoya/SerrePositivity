module

public import SerrePositivity.InfinityCategories.F2.Ind.UniverseCocartesianFibration
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedDensityRelativeFamilyImage
public import SerrePositivity.InfinityCategories.F1B.KanGlobalColimitFiberAssembly

/-!
概要：元の weighted 密度図式の全 fiber の余極限を、一つの coherent 相対 join 図式へ束ねる。
方針：同じ射影の cocartesian 性を宇宙移送し、元の全 fiber の存在を既存の全族構成へ渡す。
規約：左制限は元の図式そのもの。使われ方：元の strict 分類図式との全 Kan 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の right fibration 図式の weighted 射影の宇宙移送は、追加仮定なしに cocartesian。 -/
lemma uliftWeightedRightFibrationProjection_cocartesian
    {C : SSet.{u}} [Quasicategory C] {I : Type u} [SmallCategory I]
    (F : I ⥤ RightFibrationObject C) :
    CocartesianFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) := by
  have (i : I) : Quasicategory ((rightFibrationTotalDiagram F).obj i) :=
    quasicategory_of_innerFibration (F.obj i).val.hom
  exact cocartesianFibration_ulift (weightedNerveProjection (rightFibrationTotalDiagram F))

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 同じ weighted 密度図式を左制限に持ち、全 fiber で余極限となる一つの大域図式が存在する。 -/
lemma exists_weightedDensity_globalFamily :
    ∃ H : relativeJoin ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (rightFibrationTotalDiagram F)))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) ⟶ IndInfinity κ C,
      relativeJoinInl _ _ ≫ H = weightedIndDensityDiagram κ F ∧
        ∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v H) := by
  have : CocartesianFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) :=
    uliftWeightedRightFibrationProjection_cocartesian F
  exact F1B.exists_kanGlobalColimit_diagram_with_colimit_fibers _ (weightedIndDensityDiagram κ F)
    (weightedIndDensity_allFibers_hasColimit κ F)

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 同じ一つの全族は、元の左 Kan 延長による同じ像でも全 fiber で余極限となる。 -/
lemma exists_weightedDensity_globalFamily_with_KanImage {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β) :
    ∃ H : relativeJoin ((SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveProjection (rightFibrationTotalDiagram F)))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) ⟶ IndInfinity κ C,
      relativeJoinInl _ _ ≫ H = weightedIndDensityDiagram κ F ∧
        (∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v H)) ∧
        ∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v (H ≫ G)) := by
  obtain ⟨H, hH, hc⟩ := exists_weightedDensity_globalFamily κ F
  exact ⟨H, hH, hc, weightedDensityRelativeFamily_image_colimits κ F β hβ H hH hc⟩

end SerrePositivity.InfinityCategories.F2.Ind
