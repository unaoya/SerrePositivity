module

public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

/-!
概要：Over の nerve を反対 Under の反転した nerve と比較する。
方針：通常の圏の厳密な反対同型と反対 nerve の同型を合わせる。
規約：同じ宇宙の小さい圏を扱う。
使われ方：B5 の左 Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：反対圏の Under と元の Over の反対圏は Cat 内で同型。
方針：既存の通常の反対同値の厳密な単位・余単位を使う。
規約：単なる圏同値ではなく Cat の同型を得る。
使われ方：Over の nerve の比較。 -/
def underOpOverCatIso : Cat.of (Under (op c)) ≅ Cat.of ((Over c)ᵒᵖ) where
  hom := (Under.opEquivOpOver c).functor.toCatHom
  inv := (Under.opEquivOpOver c).inverse.toCatHom
  hom_inv_id := by apply Cat.Hom.ext; rfl
  inv_hom_id := by apply Cat.Hom.ext; rfl

/-- 概要：Over の nerve は反対 Under の nerve の反転と同型。
方針：通常の反対同型を nerve と単体の反転へ写す。
規約：元の射の向きを全て反転する。
使われ方：native な slice の古典模型。 -/
def nerveOverOppositeUnderIso : nerve (Over c) ≅ (nerve (Under (op c))).op :=
  (SSet.opFunctor.mapIso (nerveFunctor.mapIso (underOpOverCatIso c)) ≪≫
    _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso (Over c)).symm

/-- 概要：反転した点図式の始域と標的を戻すと元の点図式になる。
方針：零番目の頂点の対象を評価する。
規約：頂点 c を選び直さない。
使われ方：slice の固定図式の正規化。 -/
lemma nerveOverBase_eq : (stdSimplex.opIso ⦋0⦌).inv ≫
    (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (op c)) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c := by
  apply SSet.yonedaEquiv.injective
  exact ComposableArrows.ext₀ rfl

/-- 概要：Over と反対 Under の比較は忘却射影を保つ。
方針：反対 nerve の同型の自然性と通常の反対同型を使う。
規約：標的の反転を戻した後の射を比較する。
使われ方：左 Kan の局所図式の照合。 -/
lemma nerveOverOppositeUnderIso_projection : (nerveOverOppositeUnderIso c).hom ≫
    SSet.opFunctor.map (nerveMap (Under.forget (op c))) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom =
      nerveMap (Over.forget c) := by
  apply (cancel_epi (nerveOverOppositeUnderIso c).inv).1
  rw [Iso.inv_hom_id_assoc]
  change _ = (SSet.opFunctor.map (nerveMap (Under.opEquivOpOver c).functor) ≫
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso (Over c)).hom) ≫ nerveMap (Over.forget c)
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso_natural, ← Category.assoc, ← SSet.opFunctor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
