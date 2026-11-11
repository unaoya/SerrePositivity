module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RightStraighteningLeftRecovery
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationDiagramColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ElementsDiagram

/-!
概要：元の right fibration の全空間と、同じ分類値の元の小さい right unstraightening の比較。
方針：同じ left 復元射を反転し、二重反転の標準同型で元の全空間へ戻す。
規約：元の底上の実際の射を構成し、その同じ射の ∞ 同値性を証明する。
使われ方：right 分類値の元の圏の κ-filtered 性と、元の全空間の κ-filtered 性の一致。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {B : SSet.{u}} [Quasicategory B]

/-- 元の全空間から、同じ right 分類値の元の小さい right 復元への実際の射。 -/
def rightStraighteningSmallRecovery (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    p.val.left ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraightening (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningPresheafDiagram p) :=
  (SSet.opFunctorCompOpFunctorIso.app p.val.left).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningLeftRecovery p)

/-- 同じ right 復元射は、元の底への射影を厳密に保つ。 -/
lemma rightStraighteningSmallRecovery_projection (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    rightStraighteningSmallRecovery p ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningPresheafDiagram p) = p.val.hom := by
  unfold rightStraighteningSmallRecovery _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.smallRightUnstraighteningProjection
  rw [Category.assoc, ← Category.assoc (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningLeftRecovery p)),
    ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningLeftRecovery_projection]
  have hn : SSet.opFunctor.map (SSet.opFunctor.map p.val.hom) ≫
      (SSet.opFunctorCompOpFunctorIso.app B).hom =
        (SSet.opFunctorCompOpFunctorIso.app p.val.left).hom ≫ p.val.hom :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality p.val.hom
  rw [hn, Iso.inv_hom_id_assoc]

/-- 同じ実際の right 復元射は、元の全空間の ∞ 同値。 -/
lemma rightStraighteningSmallRecovery_isQCatEquivalence (p : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (rightStraighteningSmallRecovery p) := by
  have : Quasicategory p.val.left.op := inferInstance
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightStraighteningLeftRecovery_isPrecompositionEquivalence p).isQCatEquivalence
  let e : p.val.left ≅ p.val.left.op.op :=
    (SSet.opFunctorCompOpFunctorIso.app p.val.left).symm
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence.comp he.opposite

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
