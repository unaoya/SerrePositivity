module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientContractingHoms
public import SerrePositivity.InfinityCategories.Derived.ContractingTerminalVertex

/-! # 商の指定対象に接する実写像空間の可縮性

概要：商で殺す対象への、またその対象からの dg nerve の写像空間を可縮にする。
方針：ε の収縮と全次数の原始元を、実境界の充填に適用する。
規約：局所化普遍性や商全体の安定性は別の工程。使われ方：β3 の零化の界面。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 指定対象へ入る商の dg nerve の写像空間は可縮な Kan 複体。 -/
lemma dgQuotientTargetPinchedHom_isContractibleKan
    (x : DGQuotient.QuotientObject D P) (b : P) :
    IsContractibleKan (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P) x ⟨b.val⟩) :=
  contractingTargetPinchedHom_isContractibleKan (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 指定対象から出る商の dg nerve の写像空間は可縮な Kan 複体。 -/
lemma dgQuotientSourcePinchedHom_isContractibleKan
    (b : P) (y : DGQuotient.QuotientObject D P) :
    IsContractibleKan (DGNerve.pinchedHom A (DGQuotient.QuotientObject D P) ⟨b.val⟩ y) :=
  contractingSourcePinchedHom_isContractibleKan (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 商で殺す指定対象の頂点は実際の終対象。 -/
lemma dgQuotientKilledVertex_isTerminal (b : P) :
    IsTerminalVertex (X := dgQuotientNerve A D P)
      (Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) :=
  dgNerve_contractingElement_isTerminalVertex _ (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

end SerrePositivity.InfinityCategories
