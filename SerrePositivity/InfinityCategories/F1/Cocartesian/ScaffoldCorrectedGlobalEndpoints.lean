module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldCorrectedGlobalData

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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の指定成分の共有頂点への像は、元の直接自然性と同じ始点。 -/
lemma cocartesianScaffoldCorrectedFirstGlobalIso_shared_source :
    ((cocartesianScaffoldCorrectedFirstGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)).sourceMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap := by
  exact ((cocartesianScaffoldCorrectedFirstSquare n k p q).exactComponentIso_precomp_postcomp_source
      (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldFirstCell n k) p q)).trans
    (cocartesianOriginalCellOverNaturality_source
      (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
      (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q)

/-- 最初の指定成分の共有頂点への像は、元の直接自然性と同じ終点。 -/
lemma cocartesianScaffoldCorrectedFirstGlobalIso_shared_target :
    ((cocartesianScaffoldCorrectedFirstGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)).targetMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap := by
  have h := (congrArg
    (fun m ↦ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldFirstCell n k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ m)
    (cocartesianScaffoldLocalTarget_firstMap n k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianCellOverMap
        (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
        (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl)))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ cocartesianStraighteningHomInterval p q ≫ m) h)

/-- 次の指定成分の共有頂点への像は、同じ元の直接自然性と同じ始点。 -/
lemma cocartesianScaffoldCorrectedSecondGlobalIso_shared_source :
    ((cocartesianScaffoldCorrectedSecondGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)).sourceMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap := by
  exact ((cocartesianScaffoldCorrectedSecondSquare n k p q).exactComponentIso_precomp_postcomp_source
      (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldTailCell n k) p q)).trans
    (cocartesianOriginalCellOverNaturality_source
      (scaffoldFiniteZeroVertex n)
      (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
      (cocartesianScaffoldSharedCell_tail n k) p q)

/-- 次の指定成分の共有頂点への像も、同じ元の直接自然性と同じ終点。 -/
lemma cocartesianScaffoldCorrectedSecondGlobalIso_shared_target :
    ((cocartesianScaffoldCorrectedSecondGlobalIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)).targetMap =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap := by
  have h := (congrArg
    (fun m ↦ intervalDiagramRestriction
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldTailCell n k)))
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom) ≫ m)
    (cocartesianScaffoldLocalTarget_secondMap n k p q)).trans
    (intervalDiagramOverPre_restriction
      (cocartesianStrictTransportCoherentDiagram p.val.hom)
      (cocartesianStrictTransportCoherentDiagram q.val.hom)
      (uliftOverMorphism (cocartesianCellOverMap
        (scaffoldFiniteZeroVertex n)
        (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k) (cocartesianScaffoldSharedCell_tail n k))))
  exact (Category.assoc _ _ _).trans
    (congrArg (fun m ↦ cocartesianStraighteningHomInterval p q ≫ m) h)

end SerrePositivity.InfinityCategories
