module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexCorrectedSharedComparison
public import SerrePositivity.InfinityCategories.F1.Cocartesian.TwoSimplexStrictPullback

/-!
概要：元の全 Hom から補正比較と元の分類作用による同じ二区間の pullback への二射。
方針：既存の二つの指定成分の始点・終点を同じ共有頂点の可換式で貼り合わせる。
規約：元の全相対 Hom と既存の補正成分・分類 Hom 作用を保持する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の実際の関手同型。
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
local notation "T" => cocartesianTwoSimplexLocalTarget k p q

/-- 元の全 Hom から、同じ二つの補正成分で同じ標的 pullback へ進む射。 -/
def cocartesianTwoSimplexCorrectedGlobalPullbackMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).sourceMap
    (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).sourceMap
    ((cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_source k p q).trans
      (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_source k p q).symm)

/-- 元の分類 Hom 作用の二辺への制限を同じ標的 pullback へ束ねた射。 -/
def cocartesianTwoSimplexOriginalGlobalPullbackMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((T).map WalkingCospan.Hom.inl) ((T).map WalkingCospan.Hom.inr) :=
  pullback.lift (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).targetMap
    (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).targetMap
    ((cocartesianTwoSimplexCorrectedFirstGlobalIso_shared_target k p q).trans
      (cocartesianTwoSimplexCorrectedSecondGlobalIso_shared_target k p q).symm)

/-- 補正比較の最初の射影は元の最初の補正成分。 -/
lemma cocartesianTwoSimplexCorrectedGlobalPullbackMap_fst :
    cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.fst _ _ =
      (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).sourceMap :=
  pullback.lift_fst _ _ _

/-- 補正比較の次の射影は元の次の補正成分。 -/
lemma cocartesianTwoSimplexCorrectedGlobalPullbackMap_snd :
    cocartesianTwoSimplexCorrectedGlobalPullbackMap k p q ≫ pullback.snd _ _ =
      (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).sourceMap :=
  pullback.lift_snd _ _ _

/-- 元の分類作用の最初の射影は、同じ作用の最初の辺への制限。 -/
lemma cocartesianTwoSimplexOriginalGlobalPullbackMap_fst :
    cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.fst _ _ =
      (cocartesianTwoSimplexCorrectedFirstGlobalIso k p q).targetMap :=
  pullback.lift_fst _ _ _

/-- 元の分類作用の次の射影は、同じ作用の次の辺への制限。 -/
lemma cocartesianTwoSimplexOriginalGlobalPullbackMap_snd :
    cocartesianTwoSimplexOriginalGlobalPullbackMap k p q ≫ pullback.snd _ _ =
      (cocartesianTwoSimplexCorrectedSecondGlobalIso k p q).targetMap :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
