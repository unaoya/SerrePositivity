module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldGlobalPullbackMaps

/-!
概要：同じ標的 pullback の二つの実際の射の成分を元の指定同型で結ぶ。
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

/-- 最初の射影で元の二つの実際の射を結ぶ、既存の同じ指定同型。 -/
def cocartesianScaffoldGlobalPullbackFirstComponentIso :
    FunctorIso (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.fst _ _)
      (cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.fst _ _) :=
  F2.functorIsoOfEq (cocartesianScaffoldCorrectedFirstGlobalIso n k p q)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_fst n k p q).symm
    (cocartesianScaffoldOriginalGlobalPullbackMap_fst n k p q).symm

/-- 最初の実際の射影成分の像は、同じ共有頂点の直接自然性を回収する。 -/
lemma cocartesianScaffoldGlobalPullbackFirstComponentIso_shared_heq :
    HEq ((cocartesianScaffoldGlobalPullbackFirstComponentIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianScaffoldCorrectedFirstGlobalIso n k p q)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_fst n k p q).symm
    (cocartesianScaffoldOriginalGlobalPullbackMap_fst n k p q).symm
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inl)).trans
    (cocartesianScaffoldCorrectedFirstGlobalIso_shared_heq n k p q)

/-- 次の射影で元の二つの実際の射を結ぶ、既存の同じ指定同型。 -/
def cocartesianScaffoldGlobalPullbackSecondComponentIso :
    FunctorIso (cocartesianScaffoldCorrectedGlobalPullbackMap n k p q ≫ pullback.snd _ _)
      (cocartesianScaffoldOriginalGlobalPullbackMap n k p q ≫ pullback.snd _ _) :=
  F2.functorIsoOfEq (cocartesianScaffoldCorrectedSecondGlobalIso n k p q)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_snd n k p q).symm
    (cocartesianScaffoldOriginalGlobalPullbackMap_snd n k p q).symm

/-- 次の実際の射影成分の像は、同じ共有頂点の直接自然性を回収する。 -/
lemma cocartesianScaffoldGlobalPullbackSecondComponentIso_shared_heq :
    HEq ((cocartesianScaffoldGlobalPullbackSecondComponentIso n k p q).postcomp
      ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianScaffoldSharedCell n k) p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianScaffoldCorrectedSecondGlobalIso n k p q)
    (cocartesianScaffoldCorrectedGlobalPullbackMap_snd n k p q).symm
    (cocartesianScaffoldOriginalGlobalPullbackMap_snd n k p q).symm
    ((cocartesianScaffoldLocalTarget n k p q).map WalkingCospan.Hom.inr)).trans
    (cocartesianScaffoldCorrectedSecondGlobalIso_shared_heq n k p q)

end SerrePositivity.InfinityCategories
