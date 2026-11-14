module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.DGQuotientMappingSpaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.ContractingZeroVertex

/-! # 商で殺す対象の実際の零対象性

概要：明示的 Drinfeld 商の指定対象は dg nerve の零対象となる。
方針：ε の微分方程式を一般の収縮元の始対象性・零対象性へ適用する。
規約：この零化には K-flat 性は不要。使われ方：β3 の Verdier 商の零化条件。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
variable (P : Set D)

/-- 商で殺す指定対象の頂点は実際の始対象。 -/
lemma dgQuotientKilledVertex_isInitial (b : P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isInitialVertex _ (DGQuotient.epsilonElement A D P b)
    (_root_.SerrePositivity.DifferentialGraded.DGQuotient.differential_epsilonElement A D P b)

/-- 商で殺す指定対象の頂点は実際の零対象。 -/
lemma dgQuotientKilledVertex_isZero (b : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P)) :=
  ⟨dgQuotientKilledVertex_isInitial A D P b, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledVertex_isTerminal A D P b⟩

/-- ε により構成する、商の選ばれた零頂点。 -/
def dgQuotientKilledZeroVertex (b : P) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P),
    dgQuotientKilledVertex_isInitial A D P b, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientKilledVertex_isTerminal A D P b⟩

/-- 指定部分圏に対象があれば商の dg nerve は零対象を持つ。 -/
lemma dgQuotientNerve_hasZeroVertex (b : P) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P) :=
  ⟨⟨_, dgQuotientKilledVertex_isZero A D P b⟩⟩

/-- 商包含は指定した全対象を実際の零頂点へ送る。 -/
lemma dgQuotientNerveProjection_kills (b : P) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerveProjection A D P).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val)) := by
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuotientNerve A D P)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val).map (DGQuotient.inclusion A D P))
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex b.val).map (DGQuotient.inclusion A D P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨b.val⟩ : DGQuotient.QuotientObject D P) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.injective
    rfl
  rw [he]
  exact dgQuotientKilledVertex_isZero A D P b

end SerrePositivity.InfinityCategories.Project.DerivedCategories
