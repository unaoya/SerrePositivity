module
public import SerrePositivity.InfinityCategories.Derived.ContractingElementNerve
public import SerrePositivity.InfinityCategories.DGNerve.Functor
public import SerrePositivity.DifferentialGraded.Quotient.Universal

/-! # 明示的 dg 商の nerve と指定対象の収縮

概要：path 商の dg nerve、商包含、および指定対象の恒等辺の零ホモトピーを構成する。
方針：商の ε の微分方程式を一般の収縮元の nerve 比較に適用する。
規約：標的の対象宇宙は始域と共通。局所化・安定性は未主張。使われ方：β3 の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 明示的な path 商の dg nerve。 -/
def dgQuotientNerve (P : Set D) : SSet := dgNerve A (DGQuotient.QuotientObject D P)

/-- 元の dg nerve から明示的商の nerve への写像。 -/
def dgQuotientNerveProjection (P : Set D) : dgNerve A D ⟶ dgQuotientNerve A D P :=
  dgNerve.map (DGQuotient.inclusion A D P)

/-- 指定対象の商での恒等辺は零辺とホモトピック。 -/
lemma dgQuotientNerve_id_homotopic_zero (P : Set D) (b : P) :
    Truncated.HomotopicL
      (Truncated.Edge.id (X := twoTruncation A (DGQuotient.QuotientObject D P))
        (Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)))
      (edgeOfCycle (x := Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P))
        (y := Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) 0) :=
  dgNerve_contractingElement_id_homotopic_zero _ (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

variable {D} {P : Set D} {E : Type v} [DGCategory A E]

/-- 指定収縮付き dg 関手の商への延長を nerve に移す。 -/
def dgQuotientNerveExtension (C : DGQuotient.ContractedFunctor A D P E) :
    dgQuotientNerve A D P ⟶ dgNerve A E := dgNerve.map (DGQuotient.extension A C)

/-- 指定収縮付き dg 関手の延長は、元の nerve の関手を厳密に回収する。 -/
lemma dgQuotientNerveExtension_projection (C : DGQuotient.ContractedFunctor A D P E) :
    dgQuotientNerveProjection A D P ≫ dgQuotientNerveExtension A C =
      dgNerve.map C.toDGFunctor := by
  change dgNerve.map (DGQuotient.inclusion A D P) ≫
    dgNerve.map (DGQuotient.extension A C) = _
  rw [← dgNerve.map_comp]
  exact congrArg dgNerve.map (congrArg DGQuotient.ContractedFunctor.toDGFunctor
    (DGQuotient.restrict_extension A C))

end SerrePositivity.InfinityCategories
