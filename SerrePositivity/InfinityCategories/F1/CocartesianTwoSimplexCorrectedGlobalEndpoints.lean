module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexCorrectedGlobalData

/-!
概要：元の二つの補正成分の像の端点を、同じ共有頂点の直接自然性へ照合する。
方針：始点では指定補正 path の可換式、終点では元の底上の制限の合成則を使う。
規約：元の全 Hom と同じ共有セルを保持する。
使われ方：補正成分の共有頂点への指定像の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の指定成分の共有頂点への像は、元の直接自然性と同じ始点。 -/
lemma cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source :
    ((cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)).sourceMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap := by
  exact ((cocartesianTwoSimplexCorrectedFirstSquare k p q).exactComponentIso_precomp_postcomp_source
      (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q)).trans
    (cocartesianOriginalCellOverNaturality_source
      (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
      (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q)

/-- 最初の指定成分の共有頂点への像は、元の直接自然性と同じ終点。 -/
lemma cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target :
    ((cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)).targetMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap := by
  have h := (congrArg
    (fun m ↦ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexFirstCell k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ m)
    (cocartesianTwoSimplexLocalTarget_firstMap k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianCellOverMap
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ cocartesianStraighteningHomInterval p q ≫ m) h)

/-- 次の指定成分の共有頂点への像は、同じ元の直接自然性と同じ始点。 -/
lemma cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source :
    ((cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)).sourceMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap := by
  exact ((cocartesianTwoSimplexCorrectedSecondSquare k p q).exactComponentIso_precomp_postcomp_source
      (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q)).trans
    (cocartesianOriginalCellOverNaturality_source
      (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
      (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
      (cocartesianTwoSimplexSharedCell_second k) p q)

/-- 次の指定成分の共有頂点への像も、同じ元の直接自然性と同じ終点。 -/
lemma cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target :
    ((cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)).targetMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap := by
  have h := (congrArg
    (fun m ↦ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianTwoSimplexSecondCell k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ m)
    (cocartesianTwoSimplexLocalTarget_secondMap k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianCellOverMap
        (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
        (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k) (cocartesianTwoSimplexSharedCell_second k))))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ cocartesianStraighteningHomInterval p q ≫ m) h)

end SerrePositivity.InfinityCategories
