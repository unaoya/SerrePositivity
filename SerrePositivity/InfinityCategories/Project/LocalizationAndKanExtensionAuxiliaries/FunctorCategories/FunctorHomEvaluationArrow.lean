module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の全二胞体の同じ点での評価を、元の評価関手の射の像と合わせる。
方針：同じ両端のeqToHomだけをArrowの式から外す。
規約：標的の準圏性を仮定せず、元の二胞体を保つ。
使われ方：元の全straighteningの同じ射の評価。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
noncomputable section

namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 元の全二胞体の同じ点での評価は、同じ評価関手の像と端点を含むArrowとして一致する。 -/
lemma functorHomEvaluate_arrow {K X : SSet.{u}} {U V : K ⟶ X}
    (a : FunctorHom U V) (x : K _⦋0⦌) :
    Arrow.mk (functorHomEvaluate a x) =
      Arrow.mk ((hoFunctor.map (evaluateFunctorAt (Y := X) x)).toFunctor.map a) := by
  unfold functorHomEvaluate
  simp only [← Category.assoc, Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

end
