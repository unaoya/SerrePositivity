module

public import SerrePositivity.InfinityCategories.F1.CocartesianGlobalHomCellRestriction
public import SerrePositivity.InfinityCategories.F1.CocartesianTwoSimplexGlobalPullbackMaps

/-!
概要：元の全 Hom を同じ二辺の元の全局所 Hom の pullback へ厳密に制限する。
方針：底変換の共有セルへの直接制限則で二脚を同じ共有頂点に貼り合わせる。
規約：元の全相対 Hom を保ち、分類比較や補正成分を制限の定義に入れない。
使われ方：補正比較の source Segal 射による因数分解。
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
local notation "S" => cocartesianTwoSimplexLocalSource k p q

/-- 最初の辺の元の Hom の制限は、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianTwoSimplexSourceRestriction_first_shared :
    cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q ≫
      (S).map WalkingCospan.Hom.inl =
    cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSharedCell k) p q :=
  cocartesianSingleBaseChangeHomAction_cellOver
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl p q

/-- 次の辺の元の Hom の制限も、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianTwoSimplexSourceRestriction_second_shared :
    cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q ≫
      (S).map WalkingCospan.Hom.inr =
    cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSharedCell k) p q :=
  cocartesianSingleBaseChangeHomAction_cellOver
    (cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k) p q

/-- 元の全 Hom から、同じ二辺の元の全局所 Hom の厳密な pullback への制限。 -/
def cocartesianTwoSimplexSourceRestrictionMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) :=
  pullback.lift
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q)
    (cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q)
    ((cocartesianTwoSimplexSourceRestriction_first_shared k p q).trans
      (cocartesianTwoSimplexSourceRestriction_second_shared k p q).symm)

/-- 同じ source 制限の最初の射影は元の最初の底変換。 -/
lemma cocartesianTwoSimplexSourceRestrictionMap_fst :
    cocartesianTwoSimplexSourceRestrictionMap k p q ≫ pullback.fst _ _ =
      cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexFirstCell k) p q :=
  pullback.lift_fst _ _ _

/-- 同じ source 制限の次の射影は元の次の底変換。 -/
lemma cocartesianTwoSimplexSourceRestrictionMap_snd :
    cocartesianTwoSimplexSourceRestrictionMap k p q ≫ pullback.snd _ _ =
      cocartesianSingleBaseChangeHomAction (cocartesianTwoSimplexSecondCell k) p q :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
