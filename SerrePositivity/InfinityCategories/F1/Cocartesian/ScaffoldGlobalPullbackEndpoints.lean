module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldGlobalPullbackComponents

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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の成分の共有頂点での始点は、同じ直接自然性の端点。 -/
lemma cocartesianScaffoldGlobalPullbackFirstComponent_shared_source :
    (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.fst _ _) ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_fst n k p q)).trans
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_source n k p q)

/-- 最初の成分の共有頂点での終点は、同じ直接自然性の端点。 -/
lemma cocartesianScaffoldGlobalPullbackFirstComponent_shared_target :
    (cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.fst _ _) ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)
    (cocartesianScaffoldOriginalGlobalPullbackMap_fst n k p q)).trans
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_target n k p q)

/-- 次の成分の共有頂点での始点は、同じ直接自然性の端点。 -/
lemma cocartesianScaffoldGlobalPullbackSecondComponent_shared_source :
    (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.snd _ _) ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).sourceMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_snd n k p q)).trans
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_source n k p q)

/-- 次の成分の共有頂点での終点は、同じ直接自然性の端点。 -/
lemma cocartesianScaffoldGlobalPullbackSecondComponent_shared_target :
    (cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.snd _ _) ≫
      (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr =
    (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q).targetMap :=
  (congrArg
    (fun m ↦ m ≫ (cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)
    (cocartesianScaffoldOriginalGlobalPullbackMap_snd n k p q)).trans
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_target n k p q)

end SerrePositivity.InfinityCategories
