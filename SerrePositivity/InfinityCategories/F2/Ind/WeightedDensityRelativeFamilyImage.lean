module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedIndDensityFiberImage
public import SerrePositivity.InfinityCategories.F1B.KanRelativeJoinFiberCocone

/-!
概要：元の weighted 密度図式を延ばす一つの相対 join 図式の、全 fiber の余極限性を左 Kan 像へ移す。
方針：指定した同じ fiber 余錐を元の密度図式に正規化し、全余錐の保存性を使う。
規約：大域図式の存在と、与えられた大域図式の像の普遍性を区別する。
使われ方：密度余極限の全添字上の Kan 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 元の相対 join 全図式の後合成は、同じ fiber 全余錐の後合成を厳密に回収する。 -/
lemma kanRelativeJoinFiberCocone_post_val {K B X Y : SSet.{u}}
    (p : K ⟶ B) (v : B.obj (Opposite.op (SimplexCategory.mk 0)))
    (H : relativeJoin p (𝟙 B) ⟶ X) (q : X ⟶ Y) :
    (mapJoinCocone q (F1B.kanRelativeJoinFiberCocone p v H)).val =
      (F1B.kanRelativeJoinFiberCocone p v (H ≫ q)).val := by
  change ((_ ≫ _ ≫ H) ≫ q) = _ ≫ _ ≫ (H ≫ q)
  simp only [Category.assoc]

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [PartialOrder I] [CategoryTheory.IsFiltered I] [IsCardinalFiltered I κ]
  (F : I ⥤ RightFibrationObject C) [∀ i, IsKappaFiltered κ (F.obj i).val.left]
  {D : SSet.{u + 1}} [Quasicategory D]

omit [Fact κ.IsRegular] [IsCardinalFiltered I κ] in
/-- 元の密度図式を延ばす同じ相対 join 図式の全 fiber 余極限は、左 Kan 延長の像でも余極限。 -/
lemma weightedDensityRelativeFamily_image_colimits
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D} {G : IndInfinity κ C ⟶ D}
    (β : SSet.Homotopy F₀ (indYoneda κ C ≫ G))
    (hβ : IsLeftKanExtension (indYoneda κ C) F₀ G β)
    (H : relativeJoin ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F)))
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))) ⟶ IndInfinity κ C)
    (hH : relativeJoinInl _ _ ≫ H = weightedIndDensityDiagram κ F)
    (hc : ∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v H)) :
    ∀ v, IsColimitCone (F1B.kanRelativeJoinFiberCocone _ v (H ≫ G)) := by
  intro v
  let d := coherentCoconeOfDiagramEq
    (congrArg (fun f => vertexFiberι ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (rightFibrationTotalDiagram F))) v ≫ f) hH)
    (F1B.kanRelativeJoinFiberCocone _ v H)
  have hd : IsColimitCone d := (coherentCoconeOfDiagramEq_isColimit_iff _ _).mp (hc v)
  have hGd := weightedIndDensity_allFibers_image_isColimit κ F β hβ v d hd
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mp hGd
  change d.val ≫ G = _
  dsimp only [d]
  rw [coherentCoconeOfDiagramEq_val]
  exact kanRelativeJoinFiberCocone_post_val _ v H G

end SerrePositivity.InfinityCategories.F2.Ind
