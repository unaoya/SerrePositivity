module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexGlobalPullbackComponents

/-!
概要：同じ二射の成分の共有頂点への像の端点を厳密に揃える。
方針：射影の等式だけで既存の補正成分と大域自然性の指定合成を移す。
規約：同じ元の全 Hom と元の指定値を保持する。
使われ方：pullback 上の関手同型の二つの成分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の成分の共有頂点での始点は、同じ直接自然性の端点。 -/
lemma cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_source :
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.fst _ _) ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_fst k p q)).trans
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source k p q)

/-- 最初の成分の共有頂点での終点は、同じ直接自然性の端点。 -/
lemma cocartesianTwoSimplexGlobalPullbackFirstComponent_shared_target :
    (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.fst _ _) ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_fst k p q)).trans
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target k p q)

/-- 次の成分の共有頂点での始点は、同じ直接自然性の端点。 -/
lemma cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_source :
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.snd _ _) ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).sourceMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_snd k p q)).trans
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source k p q)

/-- 次の成分の共有頂点での終点は、同じ直接自然性の端点。 -/
lemma cocartesianTwoSimplexGlobalPullbackSecondComponent_shared_target :
    (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.snd _ _) ≫
      (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q).targetMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_snd k p q)).trans
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target k p q)

end SerrePositivity.InfinityCategories
