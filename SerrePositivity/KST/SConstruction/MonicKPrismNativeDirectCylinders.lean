module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCompositeCylinders

/-! # 共通三精密化上の合成射の直接厳密化の全補正円柱
概要：合成射を直接厳密化した元の補正列を、同じ三精密化へ移して一本の円柱にする。
方針：合成射の射影で全区間を引き戻し、既存の raw 評価の厳密な回収式を使う。
規約：元の合成射の定数族を始点に保ち、零段では比較円柱全体が定数。
使われ方：BF 合成の補正円柱と共通始点を持つ、直接厳密化側の実比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 直接厳密化の元の全補正列を、同じ三精密化パラメータへ引き戻す。 -/
def monicKPrismNativeDirectCorrectionChain (n : ℕ) : FamilyHomotopyChain
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)))
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  let c := familyHomotopyChainPrecomp (nerveMap (compositionStringComposite f g))
    (monicKPrismTracedStage F (f ≫ g) n).chain
  have hs : SSet.const (X := nerve (CompositionStringParameters f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) =
      nerveMap (compositionStringComposite f g) ≫ monicKPrismRawLevelFamily n F (f ≫ g) := by
    rw [monicKPrismRawLevelFamily, SSet.comp_const]
  have ht : nerveMap (compositionStringComposite f g) ≫
      (monicKPrismTracedStage F (f ≫ g) n).val =
      nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
    rw [monicKPrismTracedRawFamily_evaluation]
  exact familyHomotopyChainSourceTransport (familyHomotopyChainTargetTransport c ht) hs

/-- 全 trace は直接厳密化の元の全区間の同じ射影で、順序も保持する。 -/
lemma monicKPrismNativeDirectCorrectionChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeDirectCorrectionChain F f g n) =
      (familyHomotopyChainTrace (monicKPrismTracedStage F (f ≫ g) n).chain).map
        ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativeDirectCorrectionChain, familyHomotopyChainSourceTransport_trace,
    familyHomotopyChainTargetTransport_trace, familyHomotopyChainPrecomp_trace]
  rfl

/-- 直接厳密化の零段にも元の補正区間はない。 -/
lemma monicKPrismNativeDirectCorrectionChain_zero_trace :
    familyHomotopyChainTrace (monicKPrismNativeDirectCorrectionChain F f g 0) = [] := by
  rw [monicKPrismNativeDirectCorrectionChain_trace]
  rfl

/-- 直接厳密化への一本の実円柱と元の全区間・全三角形の合成証人。 -/
def monicKPrismNativeDirectCorrectionData (n : ℕ) :=
  familyChainCompositeData (monicKPrismNativeDirectCorrectionChain F f g n)

/-- 合成証人に記録された全区間は、直接厳密化の元の全 trace。 -/
lemma monicKPrismNativeDirectCorrectionData_trace (n : ℕ) :
    familyChainCompositionInputTrace
        (monicKPrismNativeDirectCorrectionData F f g n).witness =
      (familyHomotopyChainTrace (monicKPrismTracedStage F (f ≫ g) n).chain).map
        ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [familyChainCompositionInputTrace_eq, monicKPrismNativeDirectCorrectionChain_trace]

/-- 零段の直接比較も、元の合成射の全時刻での定数円柱。 -/
lemma monicKPrismNativeDirectCorrectionData_zero :
    (monicKPrismNativeDirectCorrectionData F f g 0).homotopy.h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) :=
  familyChainCompositeData_constant_of_trace_nil _
    (monicKPrismNativeDirectCorrectionChain_zero_trace F f g)

end SerrePositivity.KST.SConstruction
