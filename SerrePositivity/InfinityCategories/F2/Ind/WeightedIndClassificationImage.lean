module

public import SerrePositivity.InfinityCategories.F2.Ind.NativeKanColimitTransfer
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndRelativeNativeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityImage
public import SerrePositivity.InfinityCategories.F2.Ind.StrictClassifiedIndCocone

/-!
概要：共同 weighted 分類図式の任意の指定余極限余錐を左 Kan 延長が保存する。
方針：同じ相対 join 族の左右の native 全余錐比較と weighted 全密度余錐を使う。
規約：元の全余錐の像を扱い、一般保存性を仮定しない。
使われ方：元の strict 分類標準余錐への保存性の帰還。
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
  {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C)
  (hF : ∀ v, IsIndVertex κ C
    ((strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app (Opposite.op ⦋0⦌) v))

/-- 同じ共同分類の指定 native 余極限余錐の左 Kan 像は余極限。 -/
lemma weightedIndClassification_image_isColimit
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    (c : JoinCocone (weightedIndClassification κ F hF)) (hc : IsColimitCone c) :
    IsColimitCone (mapJoinCocone G c) := by
  let : IsFiltered I := isFiltered_of_isCardinalFiltered I κ
  let : ∀ i, IsKappaFiltered κ (F.obj i).val.left :=
    strictClassifiedIndDiagram_total_isKappaFiltered κ F hF
  let p := weightedIndDensityIndexProjection F
  let H := weightedIndDensityRelativeDiagram κ F hF
  let hl := weightedIndDensityRelativeDiagram_left_standard κ F hF
  let hr := weightedIndDensityRelativeDiagram_right κ F hF
  let d := coherentCoconeOfDiagramEq hl.symm (weightedIndDensityCocone κ F)
  let c' := coherentCoconeOfDiagramEq hr.symm c
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp
    (weightedIndDensityCocone_isColimit κ F)
  have hGd : IsColimitCone (mapJoinCocone G d) :=
    (mapJoinCocone_diagramEq_isColimit_iff G _ _).mpr
      (weightedIndDensity_image_isColimit κ F β hβ)
  have hc' : IsColimitCone c' := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp hc
  have hGc' := mapJoinCocone_isColimit_of_nativeRestrictions H
    (relativeJoinInl p (𝟙 _)) (relativeJoinInr p (𝟙 _)) G
    (weightedIndDensityRelativeDiagram_nativeRestriction_isQCatEquivalence κ F hF)
    (weightedIndDensityRelativeDiagram_image_nativeRestriction_isQCatEquivalence κ F hF β hβ)
    (relativeJoinInr_nativeRestriction_isQCatEquivalence p H)
    (relativeJoinInr_nativeRestriction_isQCatEquivalence p (H ≫ G)) d hd hGd c' hc'
  exact (mapJoinCocone_diagramEq_isColimit_iff G hr.symm c).mp hGc'

end SerrePositivity.InfinityCategories.F2.Ind
