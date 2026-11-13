module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGAlgebraPerfectInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGAlgebraMoritaInfinity
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGPerfectMoritaInfinity
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex DifferentialGraded SSet
variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
/-- dg 代数の射に沿う、実 Perf ∞ 圏上の相対 tensor。 -/
def dgAlgebraPerfectExtensionInfinity (f : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory R B ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectInfinityCategory R C :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)
/-- Perf 上の相対 tensor は完全。 -/
theorem dgAlgebraPerfectExtensionInfinity_isExactFunctor (f : B ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (dgAlgebraPerfectExtensionInfinity R f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity_isExactFunctor R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)
/-- Morita 射に沿う Perf の実相対 tensor は ∞ 圏同値。 -/
theorem dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita (f : B ⟶ C)
    [(dgDerivedExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)).IsEquivalence] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgAlgebraPerfectExtensionInfinity R f) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectExtensionInfinity_isQCatEquivalence_of_morita R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)
/-- 準同型な非可換 dg 代数の Perf は、実相対 tensor により ∞ 圏同値。 -/
theorem dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_quasiIso (f : B ⟶ C)
    (hf : QuasiIso f.hom) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgAlgebraPerfectExtensionInfinity R f) := by
  have : (dgDerivedExtension R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)).IsEquivalence :=
    (dgFunctorDerivedEquivalence R _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap_quasiEquivalence R f hf)).isEquivalence_functor
  exact dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita R f
end SerrePositivity.InfinityCategories.Project.DerivedCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Lemma 1.10" (partial := component) "仮定：線形 dg 模型、生成条件または Morita の証人（Lean が強い）。結論：特定の生成元の End と perfect 商の比較、Morita からの ∞ 圏同値。E₁ 環スペクトル全体の充満忠実な関手と本質像は得ない（Lean が弱い）。"] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraPerfectExtensionInfinity_isQCatEquivalence_of_morita
