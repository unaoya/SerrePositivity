module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakComparisonFullyFaithfulInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSpanCoherentContraction

/-!
概要：Sp 正本の一般 Verdier 分数比較の充満忠実性を、元の K-6 の商比較へ適用する。
方針：正本の全終点の充満忠実性と既存の元の実右逆・成分比較を合成する。
規約：元の IsVerdierSequence と同じ分数比較だけを使い、一般の商 API は新設しない。
使われ方：K-6 c5 の同じ全 strict Kan 比較と元の商上の比較の可逆性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：同じ元の全 strict Kan 比較の各成分は、全写像空間の同値。
方針：Sp 正本の同じ分数比較の充満忠実性と元の実右逆による本質的全射性を使う。
規約：新しい充満忠実性や比較の存在入力は追加しない。
使われ方：K-6 の同じ全単体圏上の比較の可逆性。 -/
theorem weakSpanKanMappingComparison_value_isQCatEquivalence
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanDiagram i x).obj c).obj)
      (Y := ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionSimplexKanMappingDiagram q.hom x).obj c).obj)
      ((weakSpanKanMappingComparison h x).app c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (weakSpanKanMappingComparison_value_isFullyFaithful_of_fraction h x c
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionMappingComparison_isFullyFaithful h x _))
    (weakSpanKanMappingComparison_value_isEssentiallySurjective h x c)

/-- 概要：元の一般 Verdier 分数写像空間比較は、元の同じ実射の全写像空間で同値。
方針：同じ零単体添字の strict Kan 成分の同値を、既存の元の比較の判定へ戻す。
規約：一般分数比較の充満忠実性の証明は Sp 正本だけを使う。
使われ方：K-6 c5 の元の全固定終点比較の供給。 -/
theorem weakFractionMappingComparison_isQCatEquivalence (y : B.obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) := by
  have he := (weakSpanKanMappingComparison_value_equivalence_iff h x
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) y)).mp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanMappingComparison_value_isQCatEquivalence h x _)
  have hy := congrArg (fun z : B.obj _⦋0⦌ =>
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x z))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex y)
  exact hy.mp he

/-- 概要：同じ元の全 strict Kan 比較の辺は可逆。
方針：元の全終点の分数比較の同値を既存の全自然変換の可逆性判定へ渡す。
規約：元の辺の代表を選び直さない。
使われ方：初頂点降下と商上への同じ比較の回収。 -/
theorem weakSpanKanMappingComparisonEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (weakSpanKanMappingComparisonEdge h x) :=
  weakSpanKanMappingComparisonEdge_isInvertible_of_fractionComparison h x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakFractionMappingComparison_isQCatEquivalence h x)

/-- 概要：元の一般 Verdier 商上の同じ coherent な分数比較自体は可逆。
方針：Sp 正本の全終点の充満忠実性を既存の元の商上比較の判定へ代入する。
規約：元の同じ実比較を保持し、追加の存在仮定は使わない。
使われ方：K-6 c5 の同じ商図式上の全比較。商実現比較そのものとは区別する。 -/
theorem weakQuotientMappingComparison_isIso : IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakQuotientMappingComparison h x) :=
  weakQuotientMappingComparison_isIso_of_fraction_fullyFaithful h x
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierFractionMappingComparison_isFullyFaithful h x)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
