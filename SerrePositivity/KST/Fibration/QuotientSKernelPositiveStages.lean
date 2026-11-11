module
public import SerrePositivity.KST.Fibration.RelativeSQuotientZeroStage
public import SerrePositivity.KST.Fibration.QuotientSKernelInfinitySquare
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneLocalization

/-!
概要：正の各段の商比較から、元の全実現商射と実 coherent 核四角形へ接続する。
方針：零段を既証明の無条件比較で埋め、同じ Ex∞ 射の可逆性と元の引き戻し性を得る。
規約：Sp 正本が供給する正段比較に条件付き。全四角形の比較や局所化性を主張しない。
使われ方：K-6 c5 の残入力を正の段だけに揃えた、元の商核四角形の利用側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Comparison
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)

/-- 正の各段の元の商比較に条件付きで、同じ全実現商射の Ex∞ 像は全写像空間の同値。 -/
theorem relativeSQuotientKanMap_isQCatEquivalence_of_positive_stages
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
      (simplicialDiagonalFunctor.map (relativeSimplicialQuotientMap q))) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isQCatEquivalence_of_anodyneQ_isIso
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_map_localized_isIso_iff _).mpr
    (relativeSQuotientRealization_localized_isIso_of_positive_stages q hq)

/-- 正の各段の元の商比較に条件付きで、同じ全 Ex∞ coherent 核四角形が引き戻し。 -/
theorem quotientSKernelInfinitySquare_isPullback_of_positive_stages (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (hq : ∀ n : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (quotientSKernelInfinitySquare i q) :=
  quotientSKernelInfinitySquare_isPullback i q h
    (relativeSQuotientRealization_localized_isIso_of_positive_stages q hq)

end SerrePositivity.KST.Fibration
