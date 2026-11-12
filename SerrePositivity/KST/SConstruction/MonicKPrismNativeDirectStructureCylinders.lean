module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeDirectCylinders
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeStructureCylinders

/-! # 直接厳密化側の保存済み円柱の構造射像
概要：直接厳密化側の前段・次段実円柱を、元の適合円柱と端点が合う三辺にする。
方針：同じ raw 評価の strict 適合で終点の表示だけを合わせる。
規約：元の全円柱と全補正区間を保持し、成分の等号では代用しない。
使われ方：共通始点の二組の構造三角形から全段 raw 比較を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 直接厳密化側の全 raw 評価は同じ二構造合成で厳密に一致する。 -/
lemma monicKPrismNativeDirectRaw_condition (n : ℕ) :
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z))
        (n + 1)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space =
    (nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
      RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) ≫
        RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
  simpa only [Category.assoc] using congrArg
    (fun h => nerveMap (compositionStringComposite f g) ≫
      monicKPrismTracedRawFamily F (f ≫ g) ≫ h)
    (RawSpectrumMapping.evaluation_condition (kOmegaSpectrum (F.obj x))
      (kKanSequence (F.obj z)) n)

/-- 元の前段全補正の構造射像を、同じ次段射影の終点へ表示する。 -/
def monicKPrismNativeDirectPreviousStructureChain (n : ℕ) :=
  familyHomotopyChainTargetTransport
    (familyHomotopyChainMap (monicKPrismNativeDirectCorrectionChain F f g n)
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n))
    (monicKPrismNativeDirectRaw_condition F f g n).symm

/-- 保存済みの直接厳密化の前段円柱の、同じ実構造射像。 -/
def monicKPrismNativeDirectPreviousStructureCylinder (n : ℕ) :=
  familyHomotopyEndpointTransport
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeDirectCorrectionData F f g n).homotopy
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) rfl
    (monicKPrismNativeDirectRaw_condition F f g n).symm

/-- 保存済みの直接厳密化の次段円柱を、同じ源構造射へ制限する。 -/
def monicKPrismNativeDirectProjectedStructureCylinder (n : ℕ) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (monicKPrismNativeDirectCorrectionData F f g (n + 1)).homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)

/-- 元の次段全補正の同じ源構造射への制限。 -/
def monicKPrismNativeDirectProjectedStructureChain (n : ℕ) :=
  familyHomotopyChainMap (monicKPrismNativeDirectCorrectionChain F f g (n + 1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
      ((kKanSequence (F.obj z)).level (n + 1)).space)

/-- 元の適合円柱と前段の全構造射像を順に通る実全列。 -/
def monicKPrismNativeDirectStructureChain (n : ℕ) :=
  FamilyHomotopyChain.cons (monicKPrismNativeOriginalCompatibility F f g n)
    (monicKPrismNativeDirectPreviousStructureChain F f g n)

end SerrePositivity.KST.SConstruction
