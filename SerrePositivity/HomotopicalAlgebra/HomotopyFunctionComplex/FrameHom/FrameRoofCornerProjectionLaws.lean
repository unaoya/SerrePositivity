module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofCornerEvaluationPrism
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameRoofSliceWeakContractibility

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
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.SSet _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C) (Y : C)
  {E : SSet.{u}} (q : nerve C ⟶ E) (b : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q) _⦋0⦌)

lemma roofCornerSourceSliceMap_projection : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap A Y q b ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (q.app (op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y))) =
      pullback.snd _ _ ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetProjection A Y q ≫ (nerveMap A ≫ q) := by
  have h := pullback.condition
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) ≫ q))
    (g := nerveMap A ≫ q)
  simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofCornerSourceSliceMap, Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTargetSlicePointIso_projection, h]

variable {S : SSet.{u}} (f : S ⟶ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofTarget A Y q)

lemma roofQuillenDegreeNormalizationMap_inv_source :
    inv (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap A Y q b f) ≫ pullback.snd _ _ =
      pullback.fst _ _ := by
  rw [IsIso.inv_comp_eq]
  exact (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap_source A Y q b f).symm

lemma roofQuillenDegreeCornerMap_source : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap A Y q b f ≫
    pullback.snd _ _ = pullback.fst _ _ ≫ f := by
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeCornerMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sliceRoofCornerBase_snd,
    ← Category.assoc, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows.roofQuillenDegreeNormalizationMap_inv_source]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameArrows
