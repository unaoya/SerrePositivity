module
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallMorita
public import SerrePositivity.KST.SConstruction.DGOdotTargetSmallInput
public import SerrePositivity.KST.SConstruction.DGKUniverseMorita

/-! # 同じ cone 小模型への固定 S 内の Morita 辺と ν/K 像
概要：元の Yoneda の同じ実辺を固定 S 内で Morita とし、同じ ν/K 像へ接続する。
方針：証明済みの元の射の Morita 性を対象宇宙へ移し、固定界面の辺に適用する。
規約：生成条件を追加仮定にしない。使われ方：相対 K-10 の終域比較の固定界面。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => dgOdotCornerInput R d
local notation "Q" => dgOdotTargetSmallInput R d
local notation "m" => dgOdotTargetSmallYonedaInputMap R d

/-- 元の厳密 Yoneda の同じ固定 S 辺は、生成仮定なしの Morita 射。 -/
lemma dgOdotTargetSmallYonedaInputMap_isMorita :
    (quasiEquivalencePerfectExtension R (P) (Q) (m).down).IsEquivalence := by
  letI := dgOdotTargetSmallYoneda_isMorita R d
  exact dgKUniverseLiftFunctor_isMorita R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
    (DGOdotTargetSmallPerfect R d) (dgOdotTargetSmallYoneda R d)

/-- 同じ ν 辺の元の完全射は、実安定 ∞ 圏の同値。 -/
lemma dgOdotTargetSmallInputNuMap_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap
      (dgKInputStableValue R (P)) (dgKInputStableValue R (Q)) from
        dgKInputNuMap R (m)).hom := by
  letI := dgOdotTargetSmallYonedaInputMap_isMorita R d
  rw [dgKInputNuMap_eq]
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R (P) (Q) (m).down

/-- 同じ固定 K 辺の元の BF 射は、全整数次数の π 同型。 -/
lemma dgOdotTargetSmallInputKMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R (m)) := by
  letI := dgOdotTargetSmallYonedaInputMap_isMorita R d
  exact presentedPerfectDGBFMap_morita_piIsomorphism R (m)

/-- 同じ元の K 辺そのものが、Sp で可逆となる。 -/
lemma dgOdotTargetSmallInputKEdge_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).map (dgKInputK R)) := by
  letI := dgOdotTargetSmallYonedaInputMap_isMorita R d
  have h := presentedPerfectDGBFInfinityFunctor_morita_isInvertible R (m)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((presentedPerfectDGBFInfinityFunctor R).app
      (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).edge))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (m)).map (dgKInputK R)) rfl).mp h

end SerrePositivity.KST.SConstruction
