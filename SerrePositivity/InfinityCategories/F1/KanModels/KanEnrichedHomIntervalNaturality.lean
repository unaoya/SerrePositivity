module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.Coherent.HomEnrichedNaturality
public import SerrePositivity.InfinityCategories.F1.Coherent.PrismEvaluation

/-!
概要：元の右 Hom の区間族を、図式値豊穣関手の実際の作用へ移す。
方針：coherent 単体の切断制限と豊穣後合成の可換性を全次数で使う。
規約：始域の局所 Kan 性や変換空間の Kan 性を要求しない。
使われ方：反転した全 Hom の作用を、同じ二図式の標準区間族へ厳密に接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 右 Hom の元の区間族は、豊穣 Hom の作用と coherent nerve の後合成に自然。 -/
lemma coherentRightHomInterval_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    (rightMappingSpacePrism _ ≫ pinchedHomUncurry (coherentHomComparison X Y)) ≫
        coherentNerveMap F =
      (Δ[1] ◁ (SSet.uliftFunctor.{v, u}).map (F.map X Y)) ≫
        rightMappingSpacePrism _ ≫
          pinchedHomUncurry (coherentHomComparison (F.obj X) (F.obj Y)) := by
  rw [← pinchedHomToIntervalMappingSpace_uncurry,
    ← pinchedHomToIntervalMappingSpace_uncurry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ⟩
  change (coherentNerveMap F).app _
      ((intervalMappingUncurry (coherentHomComparison X Y ≫
        pinchedHomToIntervalMappingSpace _ _)).app _ (t, σ)) =
    (intervalMappingUncurry (coherentHomComparison (F.obj X) (F.obj Y) ≫
      pinchedHomToIntervalMappingSpace _ _)).app _
        (t, ((SSet.uliftFunctor.{v, u}).map (F.map X Y)).app _ σ)
  rw [pinchedHomToIntervalMappingSpace_evaluate, pinchedHomToIntervalMappingSpace_evaluate]
  let α := SimplexCategory.mkHom (coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)
  have h := ConcreteCategory.congr_hom ((coherentNerveMap F).naturality α.op)
    (coherentHomComparisonSimplex σ.down)
  change (coherentNerveMap F).app _
      ((SimplicialNerve C).map α.op (coherentHomComparisonSimplex σ.down)) =
    (SimplicialNerve D).map α.op
      ((coherentNerveMap F).app _ (coherentHomComparisonSimplex σ.down)) at h
  change (coherentNerveMap F).app _
      ((SimplicialNerve C).map α.op (coherentHomComparisonSimplex σ.down)) = _
  rw [h]
  exact congrArg ((SimplicialNerve D).map α.op)
    (coherentHomComparisonSimplex_postcomp F σ.down)

/-- 共同実現の右 Hom 区間族は、実際の図式値豊穣 Hom 作用の後の標準区間族。 -/
lemma kanEnrichedDiagramHomInterval_toEnrichedFunctor
    {C : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    {I : Type u} [SmallCategory I] (D : KanEnrichedDiagram C I) (X Y : C) :
    kanEnrichedDiagramHomInterval D X Y rfl rfl =
      (SSet.uliftFunctor.{u + 1, u}).map (D.mappingSpaceMap X Y) ≫
        kanEnrichedDiagramHomInterval (kanDiagramUniversalEnriched I)
          (D.toEnrichedFunctor.obj X) (D.toEnrichedFunctor.obj Y) rfl rfl := by
  apply intervalMappingUncurry_injective _ _
  rw [kanEnrichedDiagramHomInterval_uncurry, intervalMappingUncurry_precomp,
    kanEnrichedDiagramHomInterval_uncurry]
  have h := coherentRightHomInterval_enriched_naturality D.toEnrichedFunctor X Y
  have h' := congrArg (fun f => f ≫ kanDiagramRealization I) h
  simp only [KanEnrichedDiagram.realization,
    kanDiagramUniversalEnriched_toEnrichedFunctor, coherentNerveMap_id,
    Category.id_comp, Category.assoc] at h' ⊢
  convert h' using 1 <;> rfl

end SerrePositivity.InfinityCategories
