module
public import SerrePositivity.KST.SConstruction.DGOdotGenerators
public import SerrePositivity.KST.SConstruction.DGOdotPerfectNerve
public import SerrePositivity.KST.SConstruction.DGOdotInputMorita

/-! # 元の実 ⊙ と指定対角商の Morita 比較
概要：供給した実二生成条件を使い、元の商への実射の Morita 性を仮定なしで結論する。
方針：既存の同じ実射・同じ Perf 比較に、証明済みの左右生成条件を適用する。
規約：Perf lax pullback 同定と長方形全体は別工程。使われ方：具体的 LT の商端点。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)
local notation "I" => dgOdotQuotientInput R d
local notation "T" => DGLaxQuotientEndInput.quotientObject (I)
local notation "P" => dgOdotAlgebraInput R d
local notation "Q" => dgOdotQuotientInputVertex R d
local notation "m" => dgOdotQuotientInputMap R d

/-- 元の実商への指定 End 包含の主 Perf 延長は、実際に同値。 -/
lemma dgOdotEndInclusion_isEquivalence :
    (quasiEquivalencePerfectExtension R (I).endObject (T) (I).endInclusion).IsEquivalence :=
  dgOdotEndInclusion_isMorita R d (dgOdotGeneratorConditions R d)

/-- 元の実 ⊙ から指定商への同じ一回の主 Perf 延長は、実際に同値。 -/
lemma dgOdotAlgebraToQuotient_isEquivalence :
    (quasiEquivalencePerfectExtension R (B) (T) (dgOdotAlgebraToQuotient R d)).IsEquivalence :=
  dgOdotAlgebraToQuotient_isMorita R d (dgOdotGeneratorConditions R d)

/-- 順方向を元の実一回延長に固定した、⊙ と同じ指定商の実 Perf 同値。 -/
def dgOdotPerfectEquivalence : PerfectModuleCategory R (B) ≌ PerfectModuleCategory R (T) :=
  dgOdotAlgebraQuotientPerfectEquivalence R d (dgOdotGeneratorConditions R d)

/-- 元の実一回の dg Perf 延長の native nerve を順方向とする、同じ実同値。 -/
def dgOdotPerfectNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (B)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R (T))) :=
  dgOdotAlgebraQuotientPerfectNerveEquivalence R d (dgOdotGeneratorConditions R d)

/-- 固定 S 内でも元の ⊙→商辺の同じ主 Perf 延長が同値。 -/
lemma dgOdotInputMap_isMorita :
    (quasiEquivalencePerfectExtension R (P) (Q) (m).down).IsEquivalence :=
  dgOdotQuotientInputMap_isMorita R d (dgOdotGeneratorConditions R d)

/-- 元の固定 ν 辺の実完全射が、安定 ∞ 圏の同値を与える。 -/
lemma dgOdotInputNuMap_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R (P)) (dgKInputStableValue R (Q)) from dgKInputNuMap R (m)).hom :=
  dgOdotQuotientInputNuMap_isQCatEquivalence R d (dgOdotGeneratorConditions R d)

/-- 元の固定 K 辺の実 BF 射は、全整数次数の π 同型。 -/
lemma dgOdotInputKMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R (m)) :=
  dgOdotQuotientInputKMap_piIsomorphism R d (dgOdotGeneratorConditions R d)

/-- 元の固定 K 辺そのものが、Sp 内の可逆辺。 -/
lemma dgOdotInputKEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).map (dgKInputK R)) :=
  dgOdotQuotientInputKEdge_isInvertible R d (dgOdotGeneratorConditions R d)

end SerrePositivity.KST.SConstruction
