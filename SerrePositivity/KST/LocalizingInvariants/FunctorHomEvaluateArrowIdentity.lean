module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceConeComparison

/-!
概要：全関手比較の Arrow が恒等なら、各頂点評価の Arrow も恒等である。
方針：評価関手の Arrow 作用を使い、両端の等号輸送を含む実評価へ戻す。
規約：元の比較の評価を保持。使われ方：相対正規化の base 成分の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma functorHomEvaluate_arrow_identity {A X : SSet.{u}} [Quasicategory X]
    {F G : A ⟶ X} (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) (U : A ⟶ X) (x : A _⦋0⦌)
    (h : Arrow.mk α = Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U)))) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate α x) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (U.app (Opposite.op ⦋0⦌) x))) := by
  let E := (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) x)).toFunctor
  have he := congrArg E.mapArrow.obj h
  exact (SliceConeComparison.evaluate_arrow α x).trans (he.trans
    ((SliceConeComparison.evaluate_arrow (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U))) x).symm.trans
      (congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_id U x))))

end SerrePositivity.KST.LocalizingInvariants
