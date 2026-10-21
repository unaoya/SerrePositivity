module

public import SerrePositivity.InfinityCategories.F1.CocartesianScaffoldCellCospan
public import SerrePositivity.InfinityCategories.F1.ScaffoldBridgeOverPushout

/-!
概要：最初の辺と尾部の同じ比較を、分類先と同じ宇宙の元の底へ写す。
方針：有限鎖の宇宙比較を後置し、二射影を元のセルの持ち上げへ同定する。
規約：元の通常関手と共有セルを保持する。
使われ方：高次単体で分類先の同じ Segal 制限の自明 Kan 性。
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

/-- 分類先と同じ宇宙の、元のセル上の最初の辺と尾部の比較。 -/
def cocartesianScaffoldLargeBridge :=
  scaffoldFiniteNerveBridge.{u + 1} n ≫ (scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom ≫
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap k)

/-- 大きい比較の最初の射影は、元の最初の辺の持ち上げ。 -/
lemma cocartesianScaffoldLargeBridge_inl :
    pushout.inl _ _ ≫ cocartesianScaffoldLargeBridge n k =
      (localKanDiagramBaseIso.{u} 1).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldFirstCell n k)) := by
  dsimp only [cocartesianScaffoldLargeBridge]
  rw [← Category.assoc (pushout.inl _ _), scaffoldFiniteNerveBridge_inl,
    Category.assoc, ← Category.assoc (nerveMap (scaffoldFiniteFirstEdge n)),
    scaffoldFiniteNerveUniverseIso_first]
  simp only [scaffoldFiniteNerveUniverseIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← CategoryTheory.Functor.map_comp]
  rfl

/-- 大きい比較の尾部射影も、元の尾部セルの持ち上げ。 -/
lemma cocartesianScaffoldLargeBridge_inr :
    pushout.inr _ _ ≫ cocartesianScaffoldLargeBridge n k =
      (scaffoldFiniteNerveUniverseIso.{u} n).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cocartesianScaffoldTailCell n k)) := by
  dsimp only [cocartesianScaffoldLargeBridge]
  rw [← Category.assoc (pushout.inr _ _), scaffoldFiniteNerveBridge_inr,
    ← Category.assoc, scaffoldFiniteNerveUniverseIso_tail, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  rfl

/-- 恒等セル上の同じ大きい比較は inner anodyne。 -/
lemma cocartesianScaffoldLargeBridge_id_innerAnodyne :
    innerAnodyneExtensions (cocartesianScaffoldLargeBridge n (𝟭 (ULift.{u} (Fin (n + 2))))) := by
  change innerAnodyneExtensions (scaffoldFiniteNerveBridge.{u + 1} n ≫
    (scaffoldFiniteNerveUniverseIso.{u} (n + 1)).hom ≫
      (SSet.uliftFunctor.{u + 1, u}).map (𝟙 _))
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact innerAnodyneExtensions.comp_mem _ _ (scaffoldFiniteNerveBridge_innerAnodyne n)
    (innerAnodyneExtensions.of_isIso _)

end SerrePositivity.InfinityCategories
