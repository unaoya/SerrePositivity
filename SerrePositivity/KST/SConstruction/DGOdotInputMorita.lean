module
public import SerrePositivity.KST.SConstruction.DGOdotInputTriangle
public import SerrePositivity.KST.SConstruction.DGKUniverseMorita

/-! # 固定 S 内の元の ⊙→商辺の Morita 性
概要：同じ実商比較辺を S 内で Morita 射とし、元の ν・K 像へ接続する。
方針：元の実射の Morita 性を対象宇宙へ移し、固定界面の同じ辺へ適用する。
規約：実自由生成の二条件は明示入力。使われ方：相対 LT の商端点比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => dgOdotAlgebraInput R d
local notation "Q" => dgOdotQuotientInputVertex R d
local notation "m" => dgOdotQuotientInputMap R d

/-- 同じ S 内の元の ⊙→商辺は、二生成条件の下で実 Morita 射。 -/
lemma dgOdotQuotientInputMap_isMorita (hgen : DGOdotGeneratorConditions R d) :
    (quasiEquivalencePerfectExtension R (P) (Q) (m).down).IsEquivalence := by
  letI : (quasiEquivalencePerfectExtension R
      (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)) (dgOdotQuotientInput R d).quotientObject
        (dgOdotAlgebraToQuotient R d)).IsEquivalence :=
    dgOdotAlgebraToQuotient_isMorita R d hgen
  exact dgKUniverseLiftFunctor_isMorita R
    (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (dgOdotAlgebra R d)) (dgOdotQuotientInput R d).quotientObject
    (dgOdotAlgebraToQuotient R d)

/-- 同じ ν 辺の元の完全射は、実安定 ∞ 圏の同値。 -/
lemma dgOdotQuotientInputNuMap_isQCatEquivalence (hgen : DGOdotGeneratorConditions R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R (P)) (dgKInputStableValue R (Q)) from
        dgKInputNuMap R (m)).hom := by
  letI := dgOdotQuotientInputMap_isMorita R d hgen
  rw [dgKInputNuMap_eq]
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R (P) (Q) (m).down

/-- 同じ固定 K 辺の実 BF 射は、全整数次数の π 同型。 -/
lemma dgOdotQuotientInputKMap_piIsomorphism (hgen : DGOdotGeneratorConditions R d) :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R (m)) := by
  letI := dgOdotQuotientInputMap_isMorita R d hgen
  exact presentedPerfectDGBFMap_morita_piIsomorphism R (m)

/-- 同じ固定 K の元の比較辺そのものは Sp で可逆。 -/
lemma dgOdotQuotientInputKEdge_isInvertible (hgen : DGOdotGeneratorConditions R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).map (dgKInputK R)) := by
  letI := dgOdotQuotientInputMap_isMorita R d hgen
  have h := presentedPerfectDGBFInfinityFunctor_morita_isInvertible R (m)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((presentedPerfectDGBFInfinityFunctor R).app
      (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).edge))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).map (dgKInputK R)) rfl).mp h

end SerrePositivity.KST.SConstruction
