module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementCriterion
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.DifferentialGraded.Functor.ModuleValued
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.ExactFunctor

/-! # dg 関手の nerve は実零対象を保存する

概要：任意の dg 関手は dg nerve の零頂点を全て保存する。
方針：零性から収縮元を回収し、dg 関手で移して像の実境界充填に使う。
規約：cofiber 保存や完全性全体は別途必要。使われ方：β3 の商関手・延長の零保存条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- dg nerve の関手は dg 対象の頂点を対象像の頂点へ送る。 -/
lemma dgFunctorNerve_vertex (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
  rfl

/-- dg 関手の像の頂点は、元の頂点の零対象性を保つ。 -/
lemma dgFunctorNerve_vertex_isZero (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x : D)
    (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) := by
  obtain ⟨h, dh⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_contractingElement x).1 hx
  rw [dgFunctorNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex _ ((F.map x x).f (-1) h)
    (F.map_contractingElement A x h dh)

/-- dg 関手の nerve は、選択によらず全ての実零頂点を保存する。 -/
lemma dgFunctorNerve_preservesZeroVertices (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesZeroVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) := by
  intro z hz
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  exact dgFunctorNerve_vertex_isZero F x hz

end SerrePositivity.InfinityCategories.Project.DerivedCategories
