module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.ScaffoldPullbackProjections

/-!
概要：部分底上の同じ scaffold 比較は、部分底の任意の射に自然。
方針：pullback の両射影で同じ可換正方形を照合する。
規約：元の底上の射として自然性を保持する。
使われ方：境界の制限と scaffold 比較の厳密な正方形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 同じ比較は任意の底上の制限に厳密に自然。 -/
lemma cocartesianScaffoldPullbackOverMap_naturality
    {C : Type u} [Category.{u} C] {E : SSet.{u}} (p : E ⟶ nerve C)
    {a b : Over (nerve C)} (f : a ⟶ b) :
    (Over.pullback (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p)) ⋙
        Over.map (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f ≫
      cocartesianScaffoldPullbackOverMap p b =
    cocartesianScaffoldPullbackOverMap p a ≫ (Over.pullback p ⋙ Over.map p).map f := by
  apply Over.OverMorphism.ext
  change (overPullbackUnderlying
      (simplicialReplacementProjection (kanCocartesianStrictTransportDiagram p))).map f ≫
        (cocartesianScaffoldPullbackOverMap p b).left =
    (cocartesianScaffoldPullbackOverMap p a).left ≫ (overPullbackUnderlying p).map f
  apply pullback.hom_ext
  · rw [Category.assoc, cocartesianScaffoldPullbackOverMap_fst,
      overPullbackUnderlying_map_fst, Category.assoc, overPullbackUnderlying_map_fst,
      ← Category.assoc, cocartesianScaffoldPullbackOverMap_fst]
  · rw [Category.assoc, cocartesianScaffoldPullbackOverMap_snd, ← Category.assoc,
      overPullbackUnderlying_map_snd, Category.assoc, overPullbackUnderlying_map_snd,
      cocartesianScaffoldPullbackOverMap_snd]

end SerrePositivity.InfinityCategories
