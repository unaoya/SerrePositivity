module

public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexGlobalPullbackMaps

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

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))

/-- 最初の射影で元の二つの実際の射を結ぶ、既存の同じ指定同型。 -/
def cocartesianTwoSimplexGlobalPullbackFirstComponentIso :
    FunctorIso (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.fst _ _)
      (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.fst _ _) :=
  F2.functorIsoOfEq (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_fst k p q).symm
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_fst k p q).symm

/-- 最初の実際の射影成分の像は、同じ共有頂点の直接自然性を回収する。 -/
lemma cocartesianTwoSimplexGlobalPullbackFirstComponentIso_shared_heq :
    HEq ((cocartesianTwoSimplexGlobalPullbackFirstComponentIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_fst k p q).symm
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_fst k p q).symm
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inl)).trans
    (cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_heq k p q)

/-- 次の射影で元の二つの実際の射を結ぶ、既存の同じ指定同型。 -/
def cocartesianTwoSimplexGlobalPullbackSecondComponentIso :
    FunctorIso (cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.snd _ _)
      (cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.snd _ _) :=
  F2.functorIsoOfEq (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_snd k p q).symm
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_snd k p q).symm

/-- 次の実際の射影成分の像は、同じ共有頂点の直接自然性を回収する。 -/
lemma cocartesianTwoSimplexGlobalPullbackSecondComponentIso_shared_heq :
    HEq ((cocartesianTwoSimplexGlobalPullbackSecondComponentIso k p q).postcomp
      ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr))
      (cocartesianBaseChangeHomNaturalityIso (cocartesianTwoSimplexSharedCell k) p q) := by
  exact (functorIsoOfEq_postcomp_heq (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q)
    (cocartesianTwoSimplexCorrectedGlobalPullbackMap_snd k p q).symm
    (cocartesianTwoSimplexOriginalGlobalPullbackMap_snd k p q).symm
    ((cocartesianTwoSimplexLocalTarget k p q).map WalkingCospan.Hom.inr)).trans
    (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_heq k p q)

end SerrePositivity.InfinityCategories
