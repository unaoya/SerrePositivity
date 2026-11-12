module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FinalHornFilledRestriction
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfFinalHornUnknownHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

/-!
# 元の右 Quillen 候補辺の Cartesian 性

概要：最終外側ホーンの二つの未知 Hom を、元の豊穣単体と相対充填へ組み立てる。
方針：全三対象の合成、全既知面への制限、薄い底の一意性を順に照合する。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の右 Quillen 候補辺の Cartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
noncomputable section
variable {C D : Type v} [Category.{u} C] [Category.{u} D]
  [SimplicialCategory C] [SimplicialCategory D] [ModelCategory C] [ModelCategory D]
  {n : ℕ} (R : EnrichedFunctor SSet.{u} D C)
  {L : C ⥤ D} (adj : L ⊣ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor R)
  [SerrePositivity.Quillen.IsLeftQuillen L]
  (cofC : MorphismProperty.FunctorialFactorizationData
    (cofibrations C) (trivialFibrations C))
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]

include SC SD in
/-- 元の右 Quillen 候補辺を固定した相対外側ホーンの全体を、元の底写像上で持ち上げる。 -/
lemma quillenCfFinalHornRight_hasLift
    (τQ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, Fin.last (n + 2)]).ι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) β)
    (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D)
    (hedge : τQ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n) =
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC Y).edge) : sq.HasLift := by
  obtain ⟨g, hz, hg, f, hf, hfg⟩ := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfFinalHornRight_relative_unknownHom_extension
    R adj cofC SC SD τQ β sq Y hedge
  let l := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFiller τQ g f hf hg hfg
  have hl : (Λ[n + 2, Fin.last (n + 2)]).ι ≫ l = τQ :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finalHornFiller_restriction τQ g f hf hg hfg hz
  refine CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := ?_ }
  apply (cancel_mono (stdSimplex.isoNerve 1).hom).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn n (Fin.last (n + 2))
  calc
    _ = (((Λ[n + 2, Fin.last (n + 2)]).ι ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ≫
        (stdSimplex.isoNerve 1).hom := by simp only [Category.assoc]
    _ = (τQ ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ≫ (stdSimplex.isoNerve 1).hom := by rw [hl]
    _ = ((Λ[n + 2, Fin.last (n + 2)]).ι ≫ β) ≫ (stdSimplex.isoNerve 1).hom :=
      congrArg (fun q ↦ q ≫ (stdSimplex.isoNerve 1).hom) sq.w
    _ = _ := Category.assoc _ _ _

include SC SD in
/-- 元の右 Quillen 置換比較の候補辺は、実際の区間射影に関して Cartesian である。 -/
lemma quillenCfRightLiftEdge_isCartesian (Y : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfRightLiftEdge R adj cofC Y).edge := by
  intro n τQ β hedge sq
  exact quillenCfFinalHornRight_hasLift R adj cofC SC SD τQ β sq Y hedge

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
