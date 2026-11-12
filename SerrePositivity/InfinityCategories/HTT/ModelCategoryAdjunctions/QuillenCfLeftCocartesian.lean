module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialHornFiller
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfInitialHornBase
public import SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfLeftLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

/-!
# 元の左 Quillen 候補辺の coCartesian 性

概要：初期外側ホーンを反転し、元の前合成条件から相対充填を構成する。
方針：後半頂点の上段性と反対豊穣圏の最終ホーン充填、薄い底の一意性を使う。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の左 Quillen 候補辺の coCartesian 性。
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
  (fibD : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations D) (fibrations D))
  (e : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.EnrichedAdjunctionHomComposition R adj)
  (SC : SerrePositivity.Enriched.TensorCotensor SSet.{u} C)
  (SD : SerrePositivity.Enriched.TensorCotensor SSet.{u} D)
  [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SC.tensor] [_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.FixedSimplicialPushoutProduct SD.tensor]

include e SC SD in
/-- 元の左 Quillen 候補辺を固定した相対初期ホーンを、元の底写像上で持ち上げる。 -/
lemma quillenCfInitialHornLeft_hasLift
    (τQ : (Λ[n + 2, 0] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.QuillenCfCollageInfinity R)
    (β : (Δ[n + 2] : SSet.{max u v}) ⟶ Δ[1])
    (sq : CommSq τQ (Λ[n + 2, 0]).ι (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) β)
    (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C)
    (hedge : τQ.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n) =
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD X).edge) : sq.HasLift := by
  obtain ⟨Y, hY⟩ := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfInitialHorn_suffix_top R τQ β sq X
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftObject R adj fibD X) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X)
    hedge (Fin.last (n + 2)) (Fin.le_last _)
  have hKan := _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollage_sHom_kanComplex R adj SC SD
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ (Fin.last (n + 2)))
  have hTF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (eHomWhiskerRight SSet
      (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornObj τQ (Fin.last (n + 2)))) := by
    rw [hY]
    exact _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftHom_trivialKanFibration R adj fibD e SD X Y
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialHornFiller_of_precomposition τQ
    (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftArrow R adj fibD X) hedge
  refine CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := ?_ }
  apply (cancel_mono (stdSimplex.isoNerve 1).hom).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn n 0
  calc
    _ = (((Λ[n + 2, 0]).ι ≫ l) ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ≫
        (stdSimplex.isoNerve 1).hom := by simp only [Category.assoc]
    _ = (τQ ≫ _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) ≫ (stdSimplex.isoNerve 1).hom := by rw [hl]
    _ = ((Λ[n + 2, 0]).ι ≫ β) ≫ (stdSimplex.isoNerve 1).hom :=
      congrArg (fun q ↦ q ≫ (stdSimplex.isoNerve 1).hom) sq.w
    _ = _ := Category.assoc _ _ _

include e SC SD in
/-- 元の左 Quillen 置換比較の候補辺は、実際の区間射影に関して coCartesian である。 -/
lemma quillenCfLeftLiftEdge_isCocartesian (X : _root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.CofibrantFibrantObjects C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfCollageProjection R) (_root_.SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions.quillenCfLeftLiftEdge R adj fibD X).edge := by
  intro n τQ β hedge sq
  exact quillenCfInitialHornLeft_hasLift R adj fibD e SC SD τQ β sq X hedge

end
end SerrePositivity.InfinityCategories.HTT.ModelCategoryAdjunctions
