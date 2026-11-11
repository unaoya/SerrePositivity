module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentFullyFaithfulReduction
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyIsoTransport

/-!
# 標準 DK 座標での比較と Core の充満忠実性

概要：標準座標での比較射の実際のホモトピー同値性が Core の充満忠実性と同値である。
方針：標準 Hom の同型による移送と標準端点の全射性の帰着を合わせる。
規約：モデル構造は既存の局所 Kan 性の同型による移送だけに使う。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の残るホモトピーの証明を A3e に接続する。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

open SSet.modelCategoryQuillen in
/-- 概要：標準座標と実際の dg pinched Hom の比較射は同じホモトピー同値性を持つ。
方針：両端の Kan 性を確認し、標準 Hom の同型との合成による判定を使う。
規約：どちら側も実際の単体的ホモトピー逆を要求する。
使われ方：Kerodon 2.5.9（Tag 00SC） の標準座標でのホモトピーを実際の比較射へ移す。 -/
lemma coherentPinchedStandardComparison_homotopyEquivalence_iff (x y : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison (R := R) x y) := by
  have : SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedHom (R := R) x y) :=
    inferInstanceAs (SSet.KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertex (R := R) y)))
  have : SSet.KanComplex (SSet.uliftFunctor.{v, u}.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y)) := by
    exact HomotopicalAlgebra.isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := R) x y).hom
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialHomotopyEquivalence_postcomp_iso_iff
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) x y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso x y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison_comp] at h
  exact h.symm

/-- 概要：比較写像の充満忠実性は全対象間の標準比較射のホモトピー同値性に等しい。
方針：固定端点の比較射での判定と標準座標への移送の同値を各対象の組で合成する。
規約：右辺を証明しない限り充満忠実性を主張しない。
使われ方：HA 1.3.1.17 の残る写像空間のホモトピー逆の正確な証明目標。 -/
lemma coherentComparison_fullyFaithful_iff_standard :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison (R := R) (D := D)) ↔
      ∀ x y : D,
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) x y) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentComparison_fullyFaithful_iff]
  exact forall_congr' (fun x ↦ forall_congr' (fun y ↦
    (coherentPinchedStandardComparison_homotopyEquivalence_iff x y).symm))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
