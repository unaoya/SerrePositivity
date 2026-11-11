module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionPerfectChoiceEquivalence
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKComparison
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance

/-!
概要：元の実懸垂の選択比較を、同じ固定 K の実 BF 比較射と全整数 π 同型へ移す。
方針：固定 ν 値の実 Perf 同値を SOA K へ送り、元の同じ固定 K 比較の順逆で挟む。
規約：固定 S・ν・K を変更しない。反復構造辺の整合や K^{nc} の模型独立性は別工程。
使われ方：K-7 d4・e の実商の模型選択比較を同じ K 値へ接続する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.NonConnective
local instance suspensionChoiceSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
section FixedComparison
variable (R : Type u) [CommRing R] (X Y : PerfDGInput.{u, v} R)
  (e : StableModelEquivalence
    (stableCategoryModel (dgKInputStableValue R X))
    (stableCategoryModel (dgKInputStableValue R Y)))

/-- 指定同値の SOA K 射を、標的の同じ実 BF K へ接続する。 -/
def dgKappaFixedKChoiceSOAMap :
    kOmegaSpectrum (stableCategoryModel (dgKInputStableValue R X)) ⟶ dgKInputSpectrum R Y :=
  kSpectrumMap e.hom ≫ presentedPerfectDGBFSOASpectrumComparison R Y

/-- 同じ標的比較の全整数 π 同型。 -/
theorem dgKappaFixedKChoiceSOAMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaFixedKChoiceSOAMap R X Y e) :=
  (kSpectrumMap_piIsomorphism_of_equivalence e).comp
    (presentedPerfectDGBFSOASpectrumComparison_piIsomorphism R Y)

/-- 同じ固定 K の順逆 BF 比較で、指定安定同値を挟む一般形。 -/
def dgKappaFixedKChoiceMap : dgKInputSpectrum R X ⟶ dgKInputSpectrum R Y :=
  presentedPerfectDGBFSOAInverseComparison R X ≫ dgKappaFixedKChoiceSOAMap R X Y e

/-- 二つの実 BF 比較を個別に検証し、元の同じ合成の全整数 π 同型へ渡す。 -/
theorem dgKappaFixedKChoiceMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaFixedKChoiceMap R X Y e) := by
  intro j
  rw [dgKappaFixedKChoiceMap, OmegaSpectrum.homotopyMap_comp]
  exact (dgKappaFixedKChoiceSOAMap_piIsomorphism R X Y e j).comp
    (presentedPerfectDGBFSOAInverseComparison_piIsomorphism R X j)
end FixedComparison

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I J : DGKappaConeInput R A κ)
  (P : DGKappaPerfectInput R A I) (Q : DGKappaPerfectInput R A J)

/-- 同じ固定 ν 値の選択同値を、同じ実安定模型の完全な順逆へ束ねる。 -/
def dgKappaSuspensionStableChoiceEquivalence :
    StableModelEquivalence
      (stableCategoryModel (dgKInputStableValue R (dgKappaSuspensionKInput R A I)))
      (stableCategoryModel (dgKInputStableValue R (dgKappaSuspensionKInput R A J))) := by
  let e := dgKappaSuspensionNuChoiceEquivalence R A I J P Q
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨⟨e.hom, preservesCofiberData_of_isExactFunctor e.hom⟩,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- 同じ二つの実懸垂の固定 K 間の、元の SOA 比較を通る実 BF 射。 -/
def dgKappaSuspensionKChoiceMap :
    dgKInputSpectrum R (dgKappaSuspensionKInput R A I) ⟶
      dgKInputSpectrum R (dgKappaSuspensionKInput R A J) :=
  dgKappaFixedKChoiceMap R (dgKappaSuspensionKInput R A I)
    (dgKappaSuspensionKInput R A J) (dgKappaSuspensionStableChoiceEquivalence R A I J P Q)

/-- 元の同じ実 BF 比較は全整数次数の π 同型。共終性や c4 の追加入力は不要。 -/
theorem dgKappaSuspensionKChoiceMap_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKappaSuspensionKChoiceMap R A I J P Q) :=
  dgKappaFixedKChoiceMap_piIsomorphism R (dgKappaSuspensionKInput R A I)
    (dgKappaSuspensionKInput R A J) (dgKappaSuspensionStableChoiceEquivalence R A I J P Q)

/-- 同じ固定 K 比較の実 Sp 辺は可逆。 -/
theorem dgKappaSuspensionKChoiceMap_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionKChoiceMap R A I J P Q)) :=
  OmegaSpectrum.isInvertible_of_piIsomorphism _
    (dgKappaSuspensionKChoiceMap_piIsomorphism R A I J P Q)

end SerrePositivity.KST.NonConnective
