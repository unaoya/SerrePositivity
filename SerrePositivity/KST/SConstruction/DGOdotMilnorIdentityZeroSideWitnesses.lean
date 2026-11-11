module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorIdentitySquareBoundary

/-!
概要：実恒等右面の零左辺・零上辺を、包含・商比較と同じ四頂点成分で比較する。
方針：同じ全対象商への二辺を回収し、零値完全関手の全自然比較を実ホモトピーにする。
規約：同じ指定零角経路を両側面で保持。D2 の存在を追加で証明したとは数えない。
使われ方：実右面の上下二胞体の全境界を同時に貼り合わせる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "PIn" => dgOdotMilnorIdentityBaseInput R d
local notation "C" => dgKInputStableValue R (PIn)
local notation "D" => dgKInputStableValue R (dgOdotMilnorIdentityDifferenceInput R d)
local notation "Z" => dgKInputStableValue R (dgFixedNullInput R (PIn))
local notation "Q" => dgKInputStableValue R (dgOdotMilnorResolvedInput R d)
local notation "hC" => dgKInputStableValue_isIdempotentComplete R _
local notation "hQ" => dgKInputStableValue_isIdempotentComplete R (dgOdotMilnorResolvedInput R d)
local notation "h₀" => perfectZeroCategory_isIdempotentComplete

/-- 概要：元の全対象商包含の同じ固定 ν 完全射。
方針：同じ入力辺を写す。規約：零角を置換しない。使われ方：実左辺の比較。 -/
def dgOdotMilnorIdentityNullLeftMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (C) (Z) :=
  dgKInputNuMap R (dgFixedNullLeft R (A := PIn))

/-- 概要：指定収縮からの元全対象商延長の同じ固定 ν 完全射。
方針：同じ実上辺を写す。規約：収縮を変えない。使われ方：実上辺の比較。 -/
def dgOdotMilnorIdentityNullTopMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) (D) :=
  dgKInputNuMap R (dgFixedNullTop R (dgOdotMilnorIdentityContracted R d))

/-- 概要：元実零角から標準零角への共有完全射。
方針：元の toZeroCategory を使う。規約：両側面で同じ射。
使われ方：指定零角の頂点経路。 -/
def dgOdotMilnorIdentityNullZeroMap : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (Z) _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory.{u + 1} := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Z)

/-- 概要：共有零角経路は元の指定 Cat^perf 頂点同型の逆そのもの。
方針：同じ全対象商零同型の逆射を回収する。
規約：別の頂点同型を選ばない。使われ方：両零側面の全比較の可逆性。 -/
lemma dgOdotMilnorIdentityNullZeroMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (perfectStableArrow (dgOdotMilnorIdentityNullZeroMap R d)
      (hC) (h₀)).toTruncated := by
  change IsIso (dgKFixedNullPerfectZeroIso R (PIn)).inv
  infer_instance

/-- 概要：元実 Cat^perf 左辺は元の全対象商包含の同じ全一単体。
方針：元四辺式と固定 ν 辺の回収を使う。規約：辺を選び直さない。
使われ方：上二胞体の実左境界の照合。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_left :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgOdotMilnorIdentityNullLeftMap R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).2.2.1]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullLeft R (A := PIn))).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgFixedNullLeft R (A := PIn)))

/-- 概要：元実 Cat^perf 上辺は元の指定収縮延長の同じ全一単体。
方針：元四辺式と固定 ν 辺の回収を使う。規約：辺を選び直さない。
使われ方：上二胞体の実上境界の照合。 -/
lemma dgOdotMilnorIdentityNullSquare_perfect_top :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ dgOdotMilnorIdentityNullSquare R d ≫ dgKInputPerfectNu R =
      SSet.yonedaEquiv.symm (perfectStableArrow
        (dgOdotMilnorIdentityNullTopMap R d) (hC) (hC)).edge := by
  rw [← Category.assoc, (dgOdotMilnorIdentityNullSquare_edges R d).2.2.2]
  change SSet.yonedaEquiv.symm ((dgKInputPerfectNu R).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgFixedNullTop R (dgOdotMilnorIdentityContracted R d))).edge) = _
  exact congrArg (fun x : perfectStableInfinity.{u + 1} _⦋1⦌ => SSet.yonedaEquiv.symm x)
    (dgKInputPerfectNu_edge R (dgFixedNullTop R (dgOdotMilnorIdentityContracted R d)))

namespace DGOdotMilnorIdentityLaxComparisonInput
variable (v : DGOdotMilnorIdentityLaxComparisonInput R d)

/-- 概要：元零左辺の全比較は包含辺と同じ始域経路・共有零角経路を持つ。
方針：標準零圏値の全関手同型を指定四辺の実ホモトピーへ運ぶ。
規約：二経路を保持。使われ方：上二胞体の指定左側面。 -/
def zeroLeftWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorIdentityNullLeftMap R d) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Q))
    (dgOdotMilnorIdentityBaseComparison R d) (dgOdotMilnorIdentityNullZeroMap R d)
    (hC) (hC) (hQ) (h₀) :=
  perfectStableArrowSquareWitness
    (dgOdotMilnorIdentityNullLeftMap R d) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Q))
    (dgOdotMilnorIdentityBaseComparison R d) (dgOdotMilnorIdentityNullZeroMap R d)
    (hC) (hC) (hQ) (h₀)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _ (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _)
      (fun _ => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

/-- 概要：元零上辺の全比較は共有零角経路と商辺と同じ終域経路を持つ。
方針：元零角の全零性と完全性から全自然比較を作り、実ホモトピーにする。
規約：二経路を保持。使われ方：上二胞体の指定上側面。 -/
def zeroTopWitness : PerfectStableArrowSquareWitness
    (dgOdotMilnorIdentityNullTopMap R d) (fromZeroCategory (Q))
    (dgOdotMilnorIdentityNullZeroMap R d) v.completedTargetMap
    (hC) (hC) (h₀) (hQ) := by
  let f := dgOdotMilnorIdentityNullTopMap R d
  let b := v.completedTargetMap
  let g := fromZeroCategory (Q)
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.hom := f.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor b.hom := b.isExact
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor g.hom := g.isExact
  apply perfectStableArrowSquareWitness f g (dgOdotMilnorIdentityNullZeroMap R d) b
    (hC) (hC) (h₀) (hQ)
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.zeroDiagramFunctorIso _ _
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := b.hom) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := f.hom) z (dgFixedNullInput_isZeroCategory R (PIn) z)))
    (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := g.hom)
      ((dgOdotMilnorIdentityNullZeroMap R d).hom.app (Opposite.op ⦋0⦌) z)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.zeroCategory_isZero _))

/-- 概要：指定零左側面は元実ホモトピーそのものによる区間全比較。
方針：同じ始域同値と共有零角逆射の可逆性を使う。
規約：元実ホモトピーを保持。使われ方：指定四境界の全比較。 -/
def zeroLeftArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgOdotMilnorIdentityNullLeftMap R d) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.toZeroCategory (Q)) (hQ) (h₀)).edge) :=
  (zeroLeftWitness R d).comparison
    (perfectStableHoArrow_isIso_of_isQCatEquivalence (dgOdotMilnorIdentityBaseComparison R d)
      (hC) (hQ) (dgOdotMilnorIdentityBaseValueEquivalence R d).isQCatEquivalence)
    (dgOdotMilnorIdentityNullZeroMap_isInvertible R d)

/-- 概要：指定零上側面は元実ホモトピーそのものによる区間全比較。
方針：共有零角逆射と同じ終域同値の可逆性を使う。
規約：元実ホモトピーを保持。使われ方：指定四境界の全比較。 -/
def zeroTopArrowComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (SSet.yonedaEquiv.symm (perfectStableArrow
      (dgOdotMilnorIdentityNullTopMap R d) (hC) (hC)).edge)
    (SSet.yonedaEquiv.symm (perfectStableArrow (fromZeroCategory (Q)) (h₀) (hQ)).edge) :=
  v.zeroTopWitness.comparison (dgOdotMilnorIdentityNullZeroMap_isInvertible R d)
    (perfectStableHoArrow_isIso_of_isQCatEquivalence v.completedTargetMap (hC) (hQ)
      (v.difference.trans (dgOdotMilnorIdentityBaseValueEquivalence R d)).isQCatEquivalence)
end DGOdotMilnorIdentityLaxComparisonInput
end SerrePositivity.KST.SConstruction
