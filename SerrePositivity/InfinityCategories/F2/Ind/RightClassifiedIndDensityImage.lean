module

public import SerrePositivity.InfinityCategories.F2.Ind.RightClassifiedIndDensityCocone
public import SerrePositivity.InfinityCategories.F2.Ind.IndLeftKanOriginalDensity
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport

/-!
概要：元の全空間による分類値の同じ密度余錐は、左 Kan 延長によって余極限へ写る。
方針：元の密度余錐の像を同じ復元同値で制限し、全余錐の値の一致で戻す。
規約：任意の filtered 保存性を仮定しない。使われ方：weighted 全空間の同じ密度余極限。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {D : SSet.{u + 1}} [Quasicategory D]

/-- 左 Kan 延長は、元の κ-filtered 全空間を添字とする同じ分類値の全密度余錐を保存する。 -/
lemma rightClassifiedIndDensity_image_isColimit
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    (p : RightFibrationObject C) [IsKappaFiltered κ p.val.left] :
    IsColimitCone (mapJoinCocone G (rightClassifiedIndDensityCocone κ p)) := by
  have hc := indLeftKanExtension_originalDensity_image_isColimit κ β hβ
    (rightStraighteningPresheafDiagram p) (rightClassified_isIndVertex κ p)
  have hr := (isColimitCone_iff_restrict_equivalentShape _
    (rightStraighteningSmallRecovery_isQCatEquivalence p).ulift
    (mapJoinCocone G (indDensityCocone κ (rightStraighteningPresheafDiagram p)
      (rightClassified_isIndVertex κ p)))).mp hc
  unfold rightClassifiedIndDensityCocone
  apply (mapJoinCocone_diagramEq_isColimit_iff G _ _).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp hr

end SerrePositivity.InfinityCategories.F2.Ind
