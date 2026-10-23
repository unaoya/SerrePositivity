module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedTwoSidedHomInterval
public import SerrePositivity.InfinityCategories.F1.Coherent.LeftIntervalNaturality

/-!
概要：共同実現した左 Hom 区間を、各対象の実際の豊穣作用で展開する。
方針：反転と宇宙持ち上げの交換を明示し、同じ左区間の豊穣自然性を使う。
規約：端点だけでなく区間と Hom の全パラメーターを保持する。
使われ方：weighted pointed prism の底の族を、元の係数の作用と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 左区間の展開は、同じ反転係数を用いた元の左区間への共同実現の後合成。 -/
lemma kanEnrichedDiagramLeftHomInterval_uncurry
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) :
    intervalMappingUncurry (kanEnrichedDiagramLeftHomInterval D X Y hF hG) =
      (Δ[1] ◁ (uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫
        coherentLeftHomInterval X Y ≫ D.realization := by
  rw [kanEnrichedDiagramLeftHomInterval, ← Category.assoc, intervalMappingPostOfEq_uncurry]
  rw [coherentLeftHomInterval]
  simp only [intervalMappingUncurry_precomp, ← Category.assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id,
    Category.id_comp]

/-- 全左区間を添字で評価すると、その添字の豊穣関手の coherent nerve を回収する。 -/
lemma kanEnrichedDiagramLeftHomInterval_evaluate
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) (i : I) :
    intervalMappingUncurry (kanEnrichedDiagramLeftHomInterval D X Y hF hG) ≫
        evaluateFunctorAt (ULift.up (nerveVertex i)) =
      (Δ[1] ◁ (uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫
        coherentLeftHomInterval X Y ≫ coherentNerveMap (D.obj i) := by
  rw [kanEnrichedDiagramLeftHomInterval_uncurry, Category.assoc, Category.assoc,
    D.realization_evaluate]

/-- 評価後の左区間の全パラメーターは、同じ対象での実際の豊穣 Hom の作用。 -/
lemma kanEnrichedDiagramLeftHomInterval_evaluate_action
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C)
    {F G : I ⥤ KanObject.{u}} (hF : D.evaluate X = F) (hG : D.evaluate Y = G) (i : I) :
    intervalMappingUncurry (kanEnrichedDiagramLeftHomInterval D X Y hF hG) ≫
        evaluateFunctorAt (ULift.up (nerveVertex i)) =
      (Δ[1] ◁ ((uliftOppositeIso (SimplicialCategory.sHom X Y)).hom ≫
        SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map ((D.obj i).map X Y)))) ≫
      coherentLeftHomInterval ((D.obj i).obj X) ((D.obj i).obj Y) := by
  rw [kanEnrichedDiagramLeftHomInterval_evaluate]
  have h := coherentLeftHomInterval_enriched_naturality (D.obj i) X Y
  have h' := congrArg (fun f =>
    (Δ[1] ◁ (uliftOppositeIso (SimplicialCategory.sHom X Y)).hom) ≫ f) h
  simpa only [whiskerLeft_comp, Category.assoc] using h'

end SerrePositivity.InfinityCategories
