module
public import SerrePositivity.KST.NonConnective.DGKappaNativeVerdier
public import SerrePositivity.KST.NonConnective.DGKappaResolvedPerfectComparison
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison

/-!
概要：同じ実小核の完備化前の K へ、元の固定 K の始点を戻す実比較を作る。
方針：元のラベル評価・D 実供給 P・同じ実核の比較を完全同値として使う。
規約：同じ I に条件付き。元の固定 K と元の P を保持し、入力間の自然性は別工程。
使われ方：K-7 c5・d3 の完備化前の連結 fibration からの実構造射の始点比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：元の固定 ν 値と完備化前の同じ実小核は、元の P を通る完全同値である。
方針：同じ実ラベル評価と同じ native P 比較を順に合成する。
規約：同じ元の全関手と二つの逆二胞体を保持する。
使われ方：完備化前の fibration の元の左項へ固定 K の始点を移す。 -/
def dgKappaNativeKernelModelEquivalence :
    StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
      (stableCategoryModel (dgKappaNativeKernelCategory R D I)) := by
  let e := (presentedPerfectDGQCatEvaluationEquivalence R D).trans
    (dgKappaPerfectResolvedComparison_isQCatEquivalence R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I)).choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨⟨e.hom, preservesCofiberData_of_isExactFunctor _⟩,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor _⟩, e.homInvIso, e.invHomIso⟩

/-- 概要：同じ左項比較の全単体写像は、元の実評価と元の P 比較の合成そのもの。
方針：構成した完全同値の順方向を回収する。
規約：元の dg 入力 D を固定した全関手の厳密等式。
使われ方：構造射の始点比較で元の P を保持する。 -/
theorem dgKappaNativeKernelModelEquivalence_hom :
    (dgKappaNativeKernelModelEquivalence R D I).hom.val =
      (presentedPerfectDGQCatEvaluationEquivalence R D).hom ≫
        dgKappaPerfectResolvedComparison R D I (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput R D I) := rfl

/-- 概要：同じ native 実核への指定完全同値による実始点比較。
方針：SOA 逆比較と同じ完全同値の K 射を合成する。
規約：K-B の同じ始点・同じ実核に限る補助定義。
使われ方：実供給 P の大きな定義を展開せずに比較を適用する。 -/
def dgKappaNativeKernelKComparisonOfEquivalence
    (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))) :=
  presentedPerfectDGBFSOAInverseComparison R D ≫ kSpectrumMap e.hom

/-- 概要：指定完全同値による同じ実始点比較は全整数 π 同型。
方針：元の SOA 比較と K の同値不変性を合成する。
規約：K-B の同じ実核に限る補助定理。
使われ方：元の P の実値への代入。 -/
private theorem nativeKernelKComparisonPi
    (e : StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
      (stableCategoryModel (dgKappaNativeKernelCategory R D I))) :
    OmegaSpectrum.PiIsomorphism (dgKappaNativeKernelKComparisonOfEquivalence R D I e) :=
  (presentedPerfectDGBFSOAInverseComparison_piIsomorphism R D).comp
    (kSpectrumMap_piIsomorphism_of_equivalence e)

/-- 概要：元の固定 K から同じ実小核の完備化前の K への実 BF 比較。
方針：元の SOA 逆比較に同じ P を通る完全同値の K 射を続ける。
規約：元の固定 K の実頂点と同じ実小核の native 値を保持する。
使われ方：完備化前の fibration の同じ左項を元の構造射の始点へ戻す。 -/
def dgKappaNativeKernelKComparison : dgKInputSpectrum R D ⟶
    kOmegaSpectrum (stableCategoryModel (dgKappaNativeKernelCategory R D I)) :=
  dgKappaNativeKernelKComparisonOfEquivalence R D I (dgKappaNativeKernelModelEquivalence R D I)

/-- 概要：元の固定 K から同じ native 実核への実始点比較は全整数 π 同型。
方針：同じ SOA 逆比較と元の P を通る完全同値の全整数同型を合成する。
規約：共終性や全入力自然性を追加入力にしない。
使われ方：K-7 c5・d3 の同じ実構造射の非負次数判定。 -/
theorem dgKappaNativeKernelKComparison_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaNativeKernelKComparison R D I) :=
  nativeKernelKComparisonPi R D I (dgKappaNativeKernelModelEquivalence R D I)

end SerrePositivity.KST.NonConnective
