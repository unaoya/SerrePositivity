module

public import SerrePositivity.EInfinity.FrameHom.FrameRoofCornerEvaluationPrism
public import SerrePositivity.EInfinity.FrameHom.FrameRoofSliceWeakContractibility

/-!
# 元の corner 比較の始域射影と同じ標的内の全図式

概要：次数正規化の逆と corner 比較を通しても、元の始域と frame 図式を厳密に回収する。
方針：既存の同型の射影式を逆向きに解き、元の引き戻しの可換性を使う。
規約：元の比較射・元の点図式・全単体を保つ。
使われ方：実 ProductHomMap の幾何的三角形の始域を標準自然変換と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Limits Opposite SSet SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (roofTarget A Y q) _⦋0⦌)

lemma roofCornerSourceSliceMap_projection : roofCornerSourceSliceMap A Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) =
      pullback.snd _ _ ≫ roofTargetProjection A Y q ≫ (nerveMap A ≫ q) := by
  have h := pullback.condition
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
    (g := nerveMap A ≫ q)
  simp only [roofCornerSourceSliceMap, Category.assoc, roofTargetSlicePointIso_projection, h]

variable {S : SSet.{u}} (f : S ⟶ roofTarget A Y q)

lemma roofQuillenDegreeNormalizationMap_inv_source :
    inv (roofQuillenDegreeNormalizationMap A Y q b f) ≫ pullback.snd _ _ =
      pullback.fst _ _ := by
  rw [IsIso.inv_comp_eq]
  exact (roofQuillenDegreeNormalizationMap_source A Y q b f).symm

lemma roofQuillenDegreeCornerMap_source : roofQuillenDegreeCornerMap A Y q b f ≫
    pullback.snd _ _ = pullback.fst _ _ ≫ f := by
  rw [roofQuillenDegreeCornerMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase_snd,
    ← Category.assoc, roofQuillenDegreeNormalizationMap_inv_source]

end SerrePositivity.EInfinity.FrameHom.FrameArrows
