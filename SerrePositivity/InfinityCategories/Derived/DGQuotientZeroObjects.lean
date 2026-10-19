module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientMappingSpaces
public import SerrePositivity.InfinityCategories.Derived.ContractingZeroVertex

/-! # 商で殺す対象の実際の零対象性

概要：明示的 Drinfeld 商の指定対象は dg nerve の零対象となる。
方針：ε の微分方程式を一般の収縮元の始対象性・零対象性へ適用する。
規約：この零化には K-flat 性は不要。使われ方：β3 の Verdier 商の零化条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 商で殺す指定対象の頂点は実際の始対象。 -/
lemma dgQuotientKilledVertex_isInitial (b : P) :
    IsInitialVertex (X := dgQuotientNerve A D P)
      (Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) :=
  dgNerve_contractingElement_isInitialVertex _ (DGQuotient.epsilonElement A D P b)
    (DGQuotient.differential_epsilonElement A D P b)

/-- 商で殺す指定対象の頂点は実際の零対象。 -/
lemma dgQuotientKilledVertex_isZero (b : P) :
    IsZeroVertex (X := dgQuotientNerve A D P)
      (Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) :=
  ⟨dgQuotientKilledVertex_isInitial A D P b, dgQuotientKilledVertex_isTerminal A D P b⟩

/-- ε により構成する、商の選ばれた零頂点。 -/
def dgQuotientKilledZeroVertex (b : P) : ZeroVertex (dgQuotientNerve A D P) :=
  ⟨Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P),
    dgQuotientKilledVertex_isInitial A D P b, dgQuotientKilledVertex_isTerminal A D P b⟩

/-- 指定部分圏に対象があれば商の dg nerve は零対象を持つ。 -/
lemma dgQuotientNerve_hasZeroVertex (b : P) : HasZeroVertex (dgQuotientNerve A D P) :=
  ⟨⟨_, dgQuotientKilledVertex_isZero A D P b⟩⟩

/-- 商包含は指定した全対象を実際の零頂点へ送る。 -/
lemma dgQuotientNerveProjection_kills (b : P) :
    IsZeroVertex (X := dgQuotientNerve A D P)
      ((dgQuotientNerveProjection A D P).app _ (Simplex.vertex b.val)) := by
  change IsZeroVertex (X := dgQuotientNerve A D P)
    ((Simplex.vertex b.val).map (DGQuotient.inclusion A D P))
  have he : (Simplex.vertex b.val).map (DGQuotient.inclusion A D P) =
      Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P) := by
    apply Simplex.vertexEquiv.injective
    rfl
  rw [he]
  exact dgQuotientKilledVertex_isZero A D P b

end SerrePositivity.InfinityCategories
