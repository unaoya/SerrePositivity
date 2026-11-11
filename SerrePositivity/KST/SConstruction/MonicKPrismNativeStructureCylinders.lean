module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeCompositeCylinders
public import SerrePositivity.KST.SConstruction.FamilyCompositeImageClasses

/-! # 保存済みの各段円柱の構造射像と元の適合円柱
概要：元の適合円柱と選んだ前段・次段円柱を、同じ三端点の三円柱として表示する。
方針：元の strict raw 評価の適合式と定数族の制限式で端点の表示だけを合わせる。
規約：保存済みの円柱の全時刻の実射を保持し、円柱を選び直さない。
使われ方：元の全辺路の比較を各段の実構造適合三角形へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の BF 合成の raw 評価の二構造合成は、全精密化で厳密に一致する。 -/
lemma monicKPrismNativeRawComposition_condition (n : ℕ) :
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
        (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space =
    (compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
  simpa only [Category.assoc] using congrArg
    (fun h => compositionStringPair f g ≫ monicKPrismTracedRawComposition F f g ≫ h)
    (RawSpectrumMapping.evaluation_condition (kOmegaSpectrum (F.obj x))
      (kKanSequence (F.obj z)) n)

/-- 元の適合円柱を、保存済み補正円柱の元の定数始点の二構造合成の間に表示する。 -/
def monicKPrismNativeOriginalCompatibility (n : ℕ) : SSet.Homotopy
    (SSet.const (X := nerve (CompositionStringParameters f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) (n + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space)
    (SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) ≫
      RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (monicKPrismRawSequenceCompatibility n F (f ≫ g))
    (nerveMap (compositionStringComposite f g))
  have hs : SSet.const (X := nerve (CompositionStringParameters f g))
      (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) (n + 1))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space =
      nerveMap (compositionStringComposite f g) ≫
        (monicKPrismRawLevelFamily (n + 1) F (f ≫ g) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
            ((kKanSequence (F.obj z)).level (n + 1)).space) := by
    rw [monicKPrismRawLevelFamily, ← Category.assoc, SSet.comp_const]
  have ht : nerveMap (compositionStringComposite f g) ≫
      (monicKPrismRawLevelFamily n F (f ≫ g) ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) =
      SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
    rw [monicKPrismRawLevelFamily, ← Category.assoc, SSet.comp_const]
  exact familyHomotopyEndpointTransport H hs ht

/-- 端点の表示を合わせても元の合成射の全適合円柱そのものを保持する。 -/
lemma monicKPrismNativeOriginalCompatibility_h (n : ℕ) :
    (monicKPrismNativeOriginalCompatibility F f g n).h =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 保存済みの前段全補正列の構造射像を、同じ次段射影の終点へ表示する。 -/
def monicKPrismNativePreviousStructureChain (n : ℕ) :=
  familyHomotopyChainTargetTransport
    (familyHomotopyChainMap (monicKPrismNativeCompositeCorrectionChain F f g n)
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n))
    (monicKPrismNativeRawComposition_condition F f g n).symm

/-- 保存済みの前段比較円柱の、同じ構造射像そのもの。 -/
def monicKPrismNativePreviousStructureCylinder (n : ℕ) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeCompositeCorrectionData F f g n).homotopy
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) rfl
    (monicKPrismNativeRawComposition_condition F f g n).symm

/-- 保存済みの次段比較円柱を、元の単射な源構造射へ制限する。 -/
def monicKPrismNativeProjectedStructureCylinder (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeCompositeCorrectionData F f g (n + 1)).homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)

end SerrePositivity.KST.SConstruction
