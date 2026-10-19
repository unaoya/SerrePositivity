module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCylinderTransport

/-! # 共通三精密化上の元の BF 合成補正列
概要：元の二入力の全補正列を、合成射の精密化も含む共通パラメータへ移す。
方針：全区間を実際に引き戻し、定数な始点の表示だけを合わせる。
規約：元の補正区間の順序と全射影 trace を保持し、零段には区間を追加しない。
使われ方：元の合成射の raw 族と BF 合成族の全段比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra Spectra.PointedMapping
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 共通三精密化上で、元の合成射の段から BF 合成の raw 評価への実補正全列。 -/
def monicKPrismNativeCompositeCorrectionChain (n : ℕ) : FamilyHomotopyChain
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)))
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) :=
  familyHomotopyChainSourceTransport
    (familyHomotopyChainPrecomp (compositionStringPair f g)
      (monicKPrismTracedCompositeCorrectionChain F f g n)) (SSet.comp_const _ _).symm

/-- 全 trace は元の各補正区間の同じパラメータ制限で、順序も保持する。 -/
lemma monicKPrismNativeCompositeCorrectionChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g n) =
      (familyHomotopyChainTrace (monicKPrismTracedCompositeCorrectionChain F f g n)).map
        ((compositionStringPair f g ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativeCompositeCorrectionChain, familyHomotopyChainSourceTransport_trace,
    familyHomotopyChainPrecomp_trace]

/-- 零段の元の補正には区間がない。 -/
lemma monicKPrismNativeCompositeCorrectionChain_zero_trace :
    familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g 0) = [] := by
  rw [monicKPrismNativeCompositeCorrectionChain_trace,
    monicKPrismTracedCompositeCorrectionChain_zero_trace, List.map_nil]

/-- 零段の BF 合成の raw 評価は、同じ元の合成射の定数族を厳密に回収する。 -/
lemma monicKPrismNativeCompositeCorrectionChain_zero :
    compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) 0 =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  (familyHomotopyChain_eq_of_trace_nil (monicKPrismNativeCompositeCorrectionChain F f g 0)
    (monicKPrismNativeCompositeCorrectionChain_zero_trace F f g)).symm

end SerrePositivity.KST.SConstruction
