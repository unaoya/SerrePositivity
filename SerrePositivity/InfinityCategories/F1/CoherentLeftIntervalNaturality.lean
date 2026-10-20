module

public import SerrePositivity.InfinityCategories.F1.CoherentLeftIntervalComparison
public import SerrePositivity.InfinityCategories.F1.CoherentLeftHomEnrichedNaturality

/-!
概要：左 Hom の区間族と豊穣関手の coherent nerve の作用の全次数の自然性。
方針：同じ左切断に制限した元の coherent 単体への後合成を比較する。
規約：係数パラメーターの反転を保ち、局所 Kan 性は要求しない。
使われ方：相対 Hom の評価と Hom の共通解像に沿う同じ辺の族の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 左 Hom の全区間族は、豊穣 Hom の実際の作用と coherent nerve 上の後合成に自然。 -/
lemma coherentLeftHomInterval_enriched_naturality
    {C D : Type v} [Category.{u} C] [Category.{u} D]
    [SimplicialCategory C] [SimplicialCategory D]
    (F : EnrichedFunctor SSet.{u} C D) (X Y : C) :
    coherentLeftHomInterval X Y ≫ coherentNerveMap F =
      (Δ[1] ◁ SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (F.map X Y))) ≫
        coherentLeftHomInterval (F.obj X) (F.obj Y) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, a⟩
  change (coherentNerveMap F).app _ ((coherentLeftHomInterval X Y).app _ (t, a)) =
    (coherentLeftHomInterval (F.obj X) (F.obj Y)).app _
      (t, (SSet.opFunctor.map ((SSet.uliftFunctor.{v, u}).map (F.map X Y))).app _ a)
  rw [coherentLeftHomInterval_evaluate, coherentLeftHomInterval_evaluate]
  let α := SimplexCategory.mkHom (coherentLeftPrismCut (stdSimplex.objEquiv t).toOrderHom)
  let σ := HomotopyLimits.coherentOppositeInverseSimplex
    (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X)
      (SSet.opObjEquiv a).down)
  have hn := ConcreteCategory.congr_hom ((coherentNerveMap F).naturality α.op) σ
  change (coherentNerveMap F).app _ ((SimplicialNerve C).map α.op σ) =
    (SimplicialNerve D).map α.op ((coherentNerveMap F).app _ σ) at hn
  change (coherentNerveMap F).app _ ((SimplicialNerve C).map α.op σ) = _
  rw [hn]
  apply congrArg ((SimplicialNerve D).map α.op)
  change (HomotopyLimits.coherentOppositeInverseSimplex
    (coherentHomComparisonSimplex (X := Opposite.op Y) (Y := Opposite.op X)
      (SSet.opObjEquiv a).down)).comp SSet F = _
  rw [coherentOppositeInverseSimplex_postcomp, coherentHomComparisonSimplex_postcomp]
  rfl

end SerrePositivity.InfinityCategories
