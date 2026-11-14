module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.InitialFinalComparisons.FinalHornHollow
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollage

/-!
概要：実際の cf Quillen 対応圏の最終外側ホーンから、端点 Hom の Kan 延長を得る。
方針：元の固定 SM7 と Quillen 条件による局所 Kan 性を同じ回収写像へ代入。
規約：Cartesian 性そのものは未主張。使われ方：候補辺に沿う前半 Hom の持ち上げ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D]
  [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory D]
  {n : ℕ} (R : EnrichedFunctor SSet.{u} D C) {L : C ⥤ D}
  (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R) [SerrePositivity.Quillen.IsLeftQuillen L]
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]

include adj SC SD in
/-- 元の cf Quillen 対応圏の最終外側ホーンから、同じ既知面を保つ Hom 延長を構成。 -/
lemma quillenCfFinalHornHollow_extension
    (τ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R) :
    ∃ g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
      (ULift.up (Fin.last (n + 2)))) ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2))),
      ∀ j, (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingPathFace (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornHollowPoint n) j).ι ≫ g =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornHollowFaceHom τ j := by
  have := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollage_sHom_kanComplex R adj SC SD (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τ (Fin.last (n + 2)))
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornHollowHom_extension τ

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
