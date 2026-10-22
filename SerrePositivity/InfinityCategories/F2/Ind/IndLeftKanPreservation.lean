module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndClassificationImage
public import SerrePositivity.InfinityCategories.F2.Ind.IndPreservationStrictReduction
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanUnitRecovery

/-!
概要：元の Yoneda に沿う左 Kan 延長は任意の小さい κ-filtered native 余極限を保存する。
方針：共同分類の全図式同型で strict 標準余錐へ移し、既存の一般保存性判定を適用する。
規約：係数全空間の κ-filtered 性は元の所属条件から証明し、追加仮定にしない。
使われ方：HTT 5.3.5.10 の実際の制限関手の本質的全射性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]
  {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
  (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
  (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
include β hβ

/-- 元の strict 分類標準余錐自身の左 Kan 像は native な余極限。 -/
lemma strictClassifiedIndCocone_image_isColimit
    {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
    (F : I ⥤ RightFibrationObject C)
    (hF : ∀ v, IsIndVertex κ C
      ((HomotopyLimits.strictCoherentDiagram F ≫ rightStraighteningInfinityMap C).app
        (Opposite.op ⦋0⦌) v)) :
    IsColimitCone (mapJoinCocone G (strictClassifiedIndCocone κ F hF)) := by
  let e : FunctorIso (weightedIndClassification κ F hF) (strictClassifiedIndDiagram κ F hF) :=
    weightedIndClassificationIso κ F hF
  have hc := strictClassifiedIndCocone_isColimit κ F hF
  have hex : HasColimit (weightedIndClassification κ F hF) :=
    (hasColimit_iff_of_functorIso e).mpr ⟨strictClassifiedIndCocone κ F hF, hc⟩
  obtain ⟨c, hc'⟩ := hex
  exact mapJoinCocone_isColimit_of_functorIso G e c (strictClassifiedIndCocone κ F hF)
    hc' hc (weightedIndClassification_image_isColimit κ F hF β hβ c hc')

/-- 元の Yoneda の指定左 Kan 延長は、任意の小さい κ-filtered native 余極限を保存する。 -/
lemma indLeftKanExtension_preservesSmallKappaFilteredColimits :
    PreservesSmallKappaFilteredColimits κ G := by
  apply (ind_preservesSmallKappaFilteredColimits_iff_strictClassified κ G).mpr
  intro I hI hκ F hF
  exact strictClassifiedIndCocone_image_isColimit κ β hβ F hF

end SerrePositivity.InfinityCategories.F2.Ind
