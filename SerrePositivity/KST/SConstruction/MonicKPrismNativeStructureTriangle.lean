module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeStructureCylinders
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeFullPathComparison
public import SerrePositivity.KST.SConstruction.FamilyChainTraceComposition

/-! # 保存済み各段円柱の元の全構造適合三角形
概要：保存済みの前段・次段円柱の構造射像と元の適合円柱を三面に持つ実三角形を得る。
方針：元の全辺路の合成式を全 trace の忠実性で移し、指定三辺の実二単体を構成する。
規約：全列の実比較から導き、構造適合や高次比較の存在を入力にしない。
使われ方：保存済み円柱を全段 raw 比較の相対持ち上げへ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet Spectra
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の適合円柱と前段の元の全補正の構造射像を順に通る実全列。 -/
def monicKPrismNativeStructureDirectChain (n : ℕ) :=
  FamilyHomotopyChain.cons (monicKPrismNativeOriginalCompatibility F f g n)
    (monicKPrismNativePreviousStructureChain F f g n)

/-- 元の全区間と同じ順序を厳密に回収する。 -/
lemma monicKPrismNativeStructureDirectChain_trace (n : ℕ) :
    familyHomotopyChainTrace (monicKPrismNativeStructureDirectChain F f g n) =
      ((nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismRawSequenceCompatibility n F (f ≫ g)).h) ::
      (familyHomotopyChainTrace (monicKPrismNativeCompositeCorrectionChain F f g n)).map
        (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  change (monicKPrismNativeOriginalCompatibility F f g n).h ::
    familyHomotopyChainTrace (monicKPrismNativePreviousStructureChain F f g n) = _
  rw [monicKPrismNativeOriginalCompatibility_h, monicKPrismNativePreviousStructureChain,
    familyHomotopyChainTargetTransport_trace, familyHomotopyChainMap_trace]
  rfl

/-- 元の全セルと共有末尾が、元の二つの全補正列の同じ合成を与える。 -/
lemma monicKPrismNativeStructureDirectChain_class (n : ℕ) :
    familyChainCompositeClass (monicKPrismNativeStructureDirectChain F f g n) =
      familyChainCompositeClass (monicKPrismNativeProjectedCorrectionChain F f g n) := by
  apply familyChainCompositeClass_transfer
    (monicKPrismNativeFullDirectPath F f g n) (monicKPrismNativeFullProjectedPath F f g n)
  · rw [monicKPrismNativeFullDirectPath_trace, monicKPrismNativeStructureDirectChain_trace]
  · exact monicKPrismNativeFullProjectedPath_trace F f g n
  · rw [monicKPrismNativeFullDirectPath_trace]
    exact List.cons_ne_nil _ _
  · exact familyTriangleStrip_class
      (familyTriangleFirst (monicKPrismCompositionNativeTriangle n F f g))
      (familyTriangleDirect (monicKPrismCompositionNativeTriangle n F f g))
      (familyTriangleCompStruct (monicKPrismCompositionNativeTriangle n F f g))
      (monicKPrismNativeSecondCompatibilityTransport F f g n)
      (monicKPrismNativeSharedTail F f g n)

/-- 保存済み前段円柱の構造射像は元の前段全列の構造射像を表す。 -/
lemma monicKPrismNativePreviousStructureCylinder_class (n : ℕ) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativePreviousStructureCylinder F f g n)) =
      familyChainCompositeClass (monicKPrismNativePreviousStructureChain F f g n) :=
  familyCompositeClass_endpointTransport _ _
    (familyChainCompositionWitness_postcomp_class
      (monicKPrismNativeCompositeCorrectionData F f g n).witness
      (RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n)) rfl _

/-- 保存済み次段円柱の源制限は元の次段全列の同じ制限を表す。 -/
lemma monicKPrismNativeProjectedStructureCylinder_class (n : ℕ) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeProjectedStructureCylinder F f g n)) =
      familyChainCompositeClass (monicKPrismNativeProjectedCorrectionChain F f g n) :=
  familyChainCompositionWitness_postcomp_class
    (monicKPrismNativeCompositeCorrectionData F f g (n + 1)).witness _

/-- 元の適合円柱・保存済み前段円柱の構造射像・次段射影を三面に持つ実三角形。 -/
def monicKPrismNativeStructureTriangle (n : ℕ) : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeOriginalCompatibility F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativePreviousStructureCylinder F f g n)))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeProjectedStructureCylinder F f g n))) := by
  apply SSet.Edge.CompStruct.ofTruncated
  apply Nonempty.some
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (monicKPrismNativeOriginalCompatibility F f g n)) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (monicKPrismNativePreviousStructureCylinder F f g n)) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (monicKPrismNativeProjectedStructureCylinder F f g n))
  rw [monicKPrismNativePreviousStructureCylinder_class,
    monicKPrismNativeProjectedStructureCylinder_class]
  exact monicKPrismNativeStructureDirectChain_class F f g n

end SerrePositivity.KST.SConstruction
