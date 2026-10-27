module
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalMoritaK
public import SerrePositivity.KST.NonConnective.DGSuspensionIterationMaps

/-!
概要：初期 Morita 射から、同じ実懸垂入力射の全反復段の Morita 保存を得る。
方針：実主 Perf 比較と実主導来比較を往復し、元の厳密商射を反復する。
規約：全単体作用や構造辺の自然性を仮定・結論しない。
使われ方：K-7 e の逐次比較が到着した際の、段別保存入力の除去。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B)
  [(quasiEquivalencePerfectExtension R A B f.down).IsEquivalence]

/-- 同じ無条件 data を反復した元の実 dg 入力射。 -/
abbrev dgSuspensionUnconditionalIterationMap :=
  dgSuspensionIterationMap R (dgKappaUnconditionalStageProvider R κ hκ)
    (dgKappaUnconditionalSuspensionMapData R κ hκ) f

/-- 初期の主 Perf Morita 射の全実反復は同じ主導来 Morita 同値となる。 -/
theorem dgSuspensionUnconditionalIterationMap_derived_isEquivalence (n : ℕ) :
    (dgDerivedExtension R _ _
      (dgSuspensionUnconditionalIterationMap R κ hκ f n).down).IsEquivalence := by
  induction n with
  | zero => exact dgKInputDerivedExtension_isEquivalence_of_perfect R A B f.down
  | succ n ih =>
    let : (dgDerivedExtension R _ _ (perfDGInputHomEquiv R _ _
        (dgSuspensionUnconditionalIterationMap R κ hκ f n))).IsEquivalence := ih
    exact dgKappaUnconditionalSuspensionDerivedExtension_isEquivalence_of_morita R κ hκ
      (dgSuspensionUnconditionalIterationMap R κ hκ f n)

/-- 初期 Morita 射だけから、同じ全実反復の主 Perf 同値性を供給する。 -/
theorem dgSuspensionUnconditionalIterationMap_perfect_isEquivalence (n : ℕ) :
    (quasiEquivalencePerfectExtension R _ _
      (dgSuspensionUnconditionalIterationMap R κ hκ f n).down).IsEquivalence := by
  cases n with
  | zero =>
    change (quasiEquivalencePerfectExtension R A B f.down).IsEquivalence
    infer_instance
  | succ n =>
    let : (dgDerivedExtension R _ _ (perfDGInputHomEquiv R _ _
        (dgSuspensionUnconditionalIterationMap R κ hκ f n))).IsEquivalence :=
      dgSuspensionUnconditionalIterationMap_derived_isEquivalence R κ hκ f n
    exact dgKappaUnconditionalSuspensionPerfectExtension_isEquivalence_of_morita R κ hκ
      (dgSuspensionUnconditionalIterationMap R κ hκ f n)

/-- 同じ全反復段の元の固定 K 射は全整数 π 同型。 -/
theorem dgSuspensionUnconditionalIterationKMap_piIsomorphism (n : ℕ) :
    OmegaSpectrum.PiIsomorphism (dgKInputSpectrumMap R
      (dgSuspensionUnconditionalIterationMap R κ hκ f n)) := by
  let := dgSuspensionUnconditionalIterationMap_perfect_isEquivalence R κ hκ f n
  exact presentedPerfectDGBFMap_morita_piIsomorphism R _

end SerrePositivity.KST.NonConnective
