module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementNerve
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration

/-! # 明示的 dg 商の nerve と指定対象の収縮

概要：path 商の dg nerve、商包含、および指定対象の恒等辺の零ホモトピーを構成する。
方針：商の ε の微分方程式を一般の収縮元の nerve 比較に適用する。
規約：標的の対象宇宙は始域と共通。局所化・安定性は未主張。使われ方：β3 の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 明示的な path 商の dg nerve。 -/
def dgQuotientNerve (P : Set D) : SSet := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGQuotient.QuotientObject D P)

/-- 明示的 dg 商の nerve は quasicategory。 -/
instance dgQuotientNerve_quasicategory (P : Set D) : Quasicategory (dgQuotientNerve A D P) :=
  inferInstanceAs (Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (DGQuotient.QuotientObject D P)))

/-- 元の dg nerve から明示的商の nerve への写像。 -/
def dgQuotientNerveProjection (P : Set D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D ⟶ dgQuotientNerve A D P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGQuotient.inclusion A D P)

/-- 指定対象の商での恒等辺は零辺とホモトピック。 -/
lemma dgQuotientNerve_id_homotopic_zero (P : Set D) (b : P) :
    Truncated.HomotopicL
      (Truncated.Edge.id (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation A (DGQuotient.QuotientObject D P))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeOfCycle (x := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P))
        (y := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) 0) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_id_homotopic_zero _ (DGQuotient.epsilonElement A D P b)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.differential_epsilonElement A D P b)

variable {D} {P : Set D} {E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

/-- 指定収縮付き dg 関手の商への延長を nerve に移す。 -/
def dgQuotientNerveExtension (C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor A D P E) :
    dgQuotientNerve A D P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGQuotient.extension A C)

/-- 指定収縮付き dg 関手の延長は、元の nerve の関手を厳密に回収する。 -/
lemma dgQuotientNerveExtension_projection (C : _root_.SerrePositivity.DifferentialGraded.DGQuotient.ContractedFunctor A D P E) :
    dgQuotientNerveProjection A D P ≫ dgQuotientNerveExtension A C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map C.toDGFunctor := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGQuotient.inclusion A D P) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (DGQuotient.extension A C) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp]
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (congrArg DGQuotient.ContractedFunctor.toDGFunctor
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.restrict_extension A C))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
