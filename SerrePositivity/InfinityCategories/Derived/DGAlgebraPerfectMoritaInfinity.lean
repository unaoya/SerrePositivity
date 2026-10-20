module
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraPerfectInfinity
public import SerrePositivity.InfinityCategories.Derived.DGAlgebraMoritaInfinity
public import SerrePositivity.InfinityCategories.Derived.DGPerfectMoritaInfinity
/-!
概要：非可換 dg 代数の Perf 上の実 tensor と、その Morita 不変性。
方針：同じ一対象 graph tensor の実 dg 制限を nerve に移す。
規約：元の Hom の平坦性を仮定しない。使われ方：β5 の Perf(A) の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory HomologicalComplex DifferentialGraded SSet
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
/-- dg 代数の射に沿う、実 Perf ∞ 圏上の相対 tensor。 -/
def dgAlgebraPerfectExtensionInfinity (f : B ⟶ C) :
    dgAlgebraPerfectInfinityCategory R B ⟶ dgAlgebraPerfectInfinityCategory R C :=
  dgPerfectExtensionInfinity R _ _ (dgAlgebraMap R f)
/-- Perf 上の相対 tensor は完全。 -/
theorem dgAlgebraPerfectExtensionInfinity_isExactFunctor (f : B ⟶ C) :
    IsExactFunctor (dgAlgebraPerfectExtensionInfinity R f) :=
  dgPerfectExtensionInfinity_isExactFunctor R _ _ (dgAlgebraMap R f)
/-- Morita 射に沿う Perf の実相対 tensor は ∞ 圏同値。 -/
theorem dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita (f : B ⟶ C)
    [(dgDerivedExtension R _ _ (dgAlgebraMap R f)).IsEquivalence] :
    IsQCatEquivalence (dgAlgebraPerfectExtensionInfinity R f) :=
  dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R _ _ (dgAlgebraMap R f)
/-- 準同型な非可換 dg 代数の Perf は、実相対 tensor により ∞ 圏同値。 -/
theorem dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso (f : B ⟶ C)
    (hf : QuasiIso f.hom) : IsQCatEquivalence (dgAlgebraPerfectExtensionInfinity R f) := by
  have : (dgDerivedExtension R _ _ (dgAlgebraMap R f)).IsEquivalence :=
    (dgFunctorDerivedEquivalence R _ _ (dgAlgebraMap R f)
      (dgAlgebraMap_quasiEquivalence R f hf)).isEquivalence_functor
  exact dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita R f
end SerrePositivity.InfinityCategories
