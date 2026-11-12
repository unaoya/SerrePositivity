module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeDirectStructureCylinders
public import SerrePositivity.KST.SConstruction.FamilyChainTraceFaithfulness
public import SerrePositivity.KST.SConstruction.MonicKPrismProjectedCompositionTrace

/-! # 直接厳密化側の保存済み各段円柱の実構造三角形
概要：直接厳密化の元の全射影 trace から、保存済み円柱の三辺の実適合を得る。
方針：元の全区間の射影式を共通パラメータへ移し、全合成証人の式を使う。
規約：補正列と円柱を選び直さず、三面を指定した実二単体を構成する。
使われ方：BF 合成側と同じ元の適合円柱を持つ二組の構造適合。
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

/-- 全次段補正の射影は、元の適合円柱と全前段補正の構造射像そのもの。 -/
lemma monicKPrismNativeDirectCorrectionChain_projection_trace (n : ℕ) :
    (familyHomotopyChainTrace (monicKPrismNativeDirectCorrectionChain F f g (n + 1))).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h) ::
      (familyHomotopyChainTrace (monicKPrismNativeDirectCorrectionChain F f g n)).map
        (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  rw [monicKPrismNativeDirectCorrectionChain_trace]
  calc
    _ = ((familyHomotopyChainTrace (monicKPrismTracedStage F (f ≫ g) (n + 1)).chain).map
        (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
          ((kKanSequence (F.obj z)).level (n + 1)).space)).map
        ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
      simp only [List.map_map, Function.comp_def, Category.assoc]
    _ = _ := by
      rw [monicKPrismTracedStage_projection_trace,
        monicKPrismNativeDirectCorrectionChain_trace]
      simp only [List.map_cons, List.map_map, Function.comp_def, Category.assoc]

/-- 射影した元の全列と、適合円柱・前段の全像を通る実列は同じ全 trace。 -/
lemma monicKPrismNativeDirectStructureChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeDirectStructureChain F f g n) =
      familyHomotopyChainTrace (monicKPrismNativeDirectProjectedStructureChain F f g n) := by
  change (monicKPrismNativeOriginalCompatibility F f g n).h ::
      familyHomotopyChainTrace (monicKPrismNativeDirectPreviousStructureChain F f g n) = _
  rw [monicKPrismNativeOriginalCompatibility_h, monicKPrismNativeDirectPreviousStructureChain,
    familyHomotopyChainTargetTransport_trace, familyHomotopyChainMap_trace,
    monicKPrismNativeDirectProjectedStructureChain, familyHomotopyChainMap_trace]
  exact (monicKPrismNativeDirectCorrectionChain_projection_trace F f g n).symm

/-- 保存済み前段円柱の像は同じ元の前段全列の構造射像を表す。 -/
lemma monicKPrismNativeDirectPreviousStructureCylinder_class (n : ℕ) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectPreviousStructureCylinder F f g n)) =
      familyChainCompositeClass (monicKPrismNativeDirectPreviousStructureChain F f g n) :=
  familyCompositeClass_endpointTransport _ _
    (familyChainCompositionWitness_postcomp_class
      (monicKPrismNativeDirectCorrectionData F f g n).witness
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) rfl _

/-- 保存済み次段円柱の源制限は元の次段全列の同じ制限を表す。 -/
lemma monicKPrismNativeDirectProjectedStructureCylinder_class (n : ℕ) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectProjectedStructureCylinder F f g n)) =
      familyChainCompositeClass (monicKPrismNativeDirectProjectedStructureChain F f g n) :=
  familyChainCompositionWitness_postcomp_class
    (monicKPrismNativeDirectCorrectionData F f g (n + 1)).witness _

/-- 同じ元の適合円柱と直接厳密化の保存済み二円柱を全三面に持つ実三角形。 -/
def monicKPrismNativeDirectStructureTriangle (n : ℕ) : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeOriginalCompatibility F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectPreviousStructureCylinder F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeDirectProjectedStructureCylinder F f g n))) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply Nonempty.some
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeOriginalCompatibility F f g n)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (monicKPrismNativeDirectPreviousStructureCylinder F f g n)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (monicKPrismNativeDirectProjectedStructureCylinder F f g n))
  rw [monicKPrismNativeDirectPreviousStructureCylinder_class,
    monicKPrismNativeDirectProjectedStructureCylinder_class]
  exact familyChainCompositeClass_eq_of_trace
    (monicKPrismNativeDirectStructureChain F f g n)
    (monicKPrismNativeDirectProjectedStructureChain F f g n)
    (monicKPrismNativeDirectStructureChain_trace F f g n)

end SerrePositivity.KST.SConstruction
