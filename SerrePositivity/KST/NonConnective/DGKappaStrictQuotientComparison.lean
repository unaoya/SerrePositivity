module
public import SerrePositivity.KST.NonConnective.DGKappaThomasonCofinality
public import SerrePositivity.KST.SConstruction.DGKNativeNuNaturality
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFQuasiEquivalence

/-!
概要：固定 ν の Perf 商辺を、元の strict 商辺と同じ宇宙下降の四角形へ戻す。
方針：K-S• 正本の Yoneda 自然性を実商へ代入し、元のラベル下降の準同値で照合する。
規約：正本の対象宇宙 u+1 の入口に特殊化する。全入力 c4・ν の Verdier 認証は要求しない。
使われ方：K-7 e の strict／Perf 商辺の接続。商を完備化同値とは扱わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, u + 1} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
local notation "C" => dgKappaResolvedConeKInput R D I
local notation "Q" => dgKappaSuspensionKInput R D I
local instance strictQuotientSourcePretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (C) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolutionSource_isDGPretriangulated R (DGKappaCone R D I)
local instance strictQuotientTargetPretriangulated : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (Q) :=
  dgKappaSuspension_isDGPretriangulated.{u, u + 1} R D I

/-- 同じ strict 商射と固定 ν の Perf 商辺の全関手自然性四角形。 -/
def dgKappaStrictQuotientNuNaturality :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (dgKNativeValueComparison R (C) ≫
      (dgKNativeInputExactMap R (C) (Q)
        ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down)).hom)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down) ≫
        dgKNativeValueComparison R (Q)) :=
  dgKNativeNuNaturality R (C) (Q) ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down)

/-- 実平坦源のラベル下降。元の全 Hom 複体を保つ。 -/
def dgKappaStrictQuotientSourceDown : dgKUniverseInput.{u, u + 1, u + 1} R (C) ⟶ C :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (C))

/-- 実商のラベル下降。元の全 Hom 複体を保つ。 -/
def dgKappaStrictQuotientTargetDown : dgKUniverseInput.{u, u + 1, u + 1} R (Q) ⟶ Q :=
  ULift.up (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown R (Q))

/-- 宇宙移送した商射を下降させると、元の同じ strict 商射を厳密に回収する。 -/
theorem dgKappaStrictQuotientInputDown_square :
    dgKNativeInputMap R (C) (Q) ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down) ≫
        dgKappaStrictQuotientTargetDown R D I =
      dgKappaStrictQuotientSourceDown R D I ≫ dgKappaResolvedSuspensionInputMap R D I := by
  apply ULift.ext
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftFunctor_comp_down.{u, u + 1, u + 1, u + 1, u + 1}
    ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down)

/-- 同じ下降四角形の固定 ν 像は、元の Perf 商辺に厳密に可換する。 -/
theorem dgKappaStrictQuotientNuDown_square :
    dgKInputNuMap R (dgKNativeInputMap R (C) (Q)
        ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down)) ≫
        dgKInputNuMap R (dgKappaStrictQuotientTargetDown R D I) =
      dgKInputNuMap R (dgKappaStrictQuotientSourceDown R D I) ≫
        dgKInputNuMap R (dgKappaResolvedSuspensionInputMap R D I) := by
  simp only [dgKInputNuMap_eq]
  change (presentedPerfectDGStableCategoryFunctor R).map _ ≫
      (presentedPerfectDGStableCategoryFunctor R).map _ =
    (presentedPerfectDGStableCategoryFunctor R).map _ ≫
      (presentedPerfectDGStableCategoryFunctor R).map _
  rw [← Functor.map_comp, ← Functor.map_comp, dgKappaStrictQuotientInputDown_square]

/-- 同じ下降四角形の固定 K 像も、元の strict 商辺に厳密に可換する。 -/
theorem dgKappaStrictQuotientKDown_square :
    CommSq (dgKInputSpectrumMap R (dgKNativeInputMap R (C) (Q)
      ((dgKappaResolvedSuspensionInputMap.{u, u + 1} R D I).down)))
      (dgKInputSpectrumMap R (dgKappaStrictQuotientSourceDown R D I))
      (dgKInputSpectrumMap R (dgKappaStrictQuotientTargetDown R D I))
      (dgKInputSpectrumMap R (dgKappaResolvedSuspensionInputMap R D I)) := by
  constructor
  rw [← presentedPerfectDGBFMap_comp, ← presentedPerfectDGBFMap_comp,
    dgKappaStrictQuotientInputDown_square]

/-- 平坦源の元の下降 K 射は全整数 π 同型。 -/
theorem dgKappaStrictQuotientSourceDown_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R (dgKappaStrictQuotientSourceDown R D I)) :=
  presentedPerfectDGBFMap_piIsomorphism_of_quasiEquivalence R _
    (dgKUniverseLiftDown_quasiEquivalence R (C))

/-- 商の元の下降 K 射も全整数 π 同型。これは商自体の完備化比較とは別の準同値。 -/
theorem dgKappaStrictQuotientTargetDown_piIsomorphism :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R (dgKappaStrictQuotientTargetDown R D I)) :=
  presentedPerfectDGBFMap_piIsomorphism_of_quasiEquivalence R _
    (dgKUniverseLiftDown_quasiEquivalence R (Q))

end SerrePositivity.KST.NonConnective
