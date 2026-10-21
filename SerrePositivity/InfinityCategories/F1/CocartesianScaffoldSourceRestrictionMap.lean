module

public import SerrePositivity.InfinityCategories.F1.CocartesianGlobalHomCellRestriction
public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldGlobalPullbackMaps

/-!
概要：元の全 Hom を同じ最初の辺と尾部の元の全局所 Hom の pullback へ厳密に制限する。
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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)
  (p q : CocartesianFibrationCategory (nerve C))
local notation "S" => cocartesianScaffoldLocalSource n k p q

/-- 最初の辺の元の Hom の制限は、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianScaffoldSourceRestriction_first_shared :
    cocartesianSingleBaseChangeHomAction (cocartesianScaffoldFirstCell n k) p q ≫
      (S).map WalkingCospan.Hom.inl =
    cocartesianSingleBaseChangeHomAction (cocartesianScaffoldSharedCell n k) p q :=
  cocartesianSingleBaseChangeHomAction_cellOver
    (cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl p q

/-- 次の辺の元の Hom の制限も、同じ共有頂点への直接制限に一致。 -/
lemma cocartesianScaffoldSourceRestriction_second_shared :
    cocartesianSingleBaseChangeHomAction (cocartesianScaffoldTailCell n k) p q ≫
      (S).map WalkingCospan.Hom.inr =
    cocartesianSingleBaseChangeHomAction (cocartesianScaffoldSharedCell n k) p q :=
  cocartesianSingleBaseChangeHomAction_cellOver
    (scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k) p q

/-- 元の全 Hom から、同じ最初の辺と尾部の元の全局所 Hom の厳密な pullback への制限。 -/
def cocartesianScaffoldSourceRestrictionMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom p q) ⟶
      pullback ((S).map WalkingCospan.Hom.inl) ((S).map WalkingCospan.Hom.inr) :=
  pullback.lift
    (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldFirstCell n k) p q)
    (cocartesianSingleBaseChangeHomAction (cocartesianScaffoldTailCell n k) p q)
    ((cocartesianScaffoldSourceRestriction_first_shared n k p q).trans
      (cocartesianScaffoldSourceRestriction_second_shared n k p q).symm)

/-- 同じ source 制限の最初の射影は元の最初の底変換。 -/
lemma cocartesianScaffoldSourceRestrictionMap_fst :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫ pullback.fst _ _ =
      cocartesianSingleBaseChangeHomAction (cocartesianScaffoldFirstCell n k) p q :=
  pullback.lift_fst _ _ _

/-- 同じ source 制限の次の射影は元の次の底変換。 -/
lemma cocartesianScaffoldSourceRestrictionMap_snd :
    cocartesianScaffoldSourceRestrictionMap n k p q ≫ pullback.snd _ _ =
      cocartesianSingleBaseChangeHomAction (cocartesianScaffoldTailCell n k) p q :=
  pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories
