module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseDuality
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OppositeSimplexYoneda
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseRightFilling
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：edgewise の左端射影の全境界充填。
方針：双対写像で左射影を反転後の右射影へ写し、同型と右射影の持ち上げ性を合成する。
規約：標的は元の Kan 複体の反転。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、Corollary 8.1.1.13（Tag 048H）、Corollary 5.6.0.6（Tag 028T）、自然な反転比較。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：双対後の右端射影は元の左端射影に等しい。
方針：重みの右包含の逆反転の式と、反転した標準単体の Yoneda の式を使う。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Remark 8.1.1.7（Tag 03JL）、左射影の持ち上げ性を右射影から移す。 -/
lemma edgewiseDuality_right (X : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.op = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (stdSimplex.obj n.unop).op (stdSimplex.obj n.unop) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReverseIso n.unop).inv ≫ SSet.opFunctor.map f) =
    SSet.opObjEquiv.symm (SSet.yonedaEquiv ((stdSimplex.opIso n.unop).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop).op (stdSimplex.obj n.unop) ≫ f))
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeightReverse_inv_inr, Category.assoc,
    ← SSet.opFunctor.map_comp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.oppositeSimplex_yoneda n.unop (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ f)

/-- 概要：Kan 複体の edgewise の左端射影も trivial Kan fibration。
方針：双対写像の同型性と反転した Kan 複体の右射影の全単射の持ち上げ性を合成する。
規約：全境界を持ち上げる性質として記録する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、空間とその反転の自然な共通解像。 -/
@[kerodon 048J]
instance edgewiseLeft_trivialKanFibration (X : SSet.{u}) [KanComplex X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X) where
  mem := by
    rw [← edgewiseDuality_right]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseDuality X) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.op)
      (MorphismProperty.of_isIso _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight X.op))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
