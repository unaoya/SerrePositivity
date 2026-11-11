module
public import SerrePositivity.KST.SConstruction.MonicKPrismProjectedCompositionTrace
public import SerrePositivity.KST.SConstruction.SpectrumCylinderComposition

/-! # 合成補正の後半の全射影 trace
概要：後続射の補正を前の同じ BF 族と合成した trace の構造射での射影を計算する。
方針：前の BF 族の厳密適合を使い、後続の保存済み射影 trace と suspension の合成保存を適用する。
規約：元の適合区間・前段の補正全区間と同じ BF 族を保持する。
使われ方：合成補正の前後二つの射影分解を合わせた構造適合の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet Spectra
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 後半補正の各実区間は、前の同じ BF 族との円柱合成そのものである。 -/
lemma monicKPrismCompositeSecondTrace_cylinders (n : ℕ) :
    monicKPrismCompositeSecondTrace F f g n =
      (familyHomotopyChainTrace (monicKPrismTracedStage F g n).chain).map
        (spectrumCylinderComposite (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y))
          ((kKanSequence (F.obj z)).level n).space n (monicKPrismTracedBFFamily F f)) := rfl

/-- 射影に現れる後続適合区間は、前の同じ BF 族の suspension と実合成する。 -/
def monicKPrismCompositeSecondCompatibility (n : ℕ) :=
  spectrumSuspendedCylinderComposite (kOmegaSpectrum (F.obj x)) (kOmegaSpectrum (F.obj y))
    ((kKanSequence (F.obj z)).level (n + 1)).space n (monicKPrismTracedBFFamily F f)
      (monicKPrismRawSequenceCompatibility n F g).h

/-- 後半補正の射影は、元の後続適合区間と前段の後半補正の段の境界比較に分解する。 -/
lemma monicKPrismCompositeSecondTrace_projection (n : ℕ) :
    (monicKPrismCompositeSecondTrace F f g (n + 1)).map
      (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum (F.obj x)).sigma n)
        ((kKanSequence (F.obj z)).level (n + 1)).space) =
      monicKPrismCompositeSecondCompatibility F f g n ::
        (monicKPrismCompositeSecondTrace F f g n).map
          (· ≫ RawSpectrumMapping.step (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n) := by
  let X := kOmegaSpectrum (F.obj x)
  let Y := kOmegaSpectrum (F.obj y)
  let Z := kKanSequence (F.obj z)
  let a := monicKPrismTracedBFFamily F f
  let S := spectrumSuspendedCylinderComposite X Y (Q := nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString g))
    (Z.level (n + 1)).space n a
  rw [monicKPrismCompositeSecondTrace_cylinders]
  calc
    _ = ((familyHomotopyChainTrace (monicKPrismTracedStage F g (n + 1)).chain).map
        (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Y.sigma n) (Z.level (n + 1)).space)).map S := by
      simp only [List.map_map, Function.comp_def]
      congr 1
      funext h
      exact spectrumCylinderComposite_projection X Y (Z.level (n + 1)).space n a h
    _ = S (monicKPrismRawSequenceCompatibility n F g).h ::
        (familyHomotopyChainTrace (monicKPrismTracedStage F g n).chain).map
          (fun h => S (h ≫ RawSpectrumMapping.step Y Z n)) := by
      rw [monicKPrismTracedStage_projection_trace]
      simp only [List.map_cons, List.map_map, Function.comp_def]
      rfl
    _ = _ := by
      rw [monicKPrismCompositeSecondTrace_cylinders]
      simp only [List.map_map, Function.comp_def]
      congr 1
      congr 1
      funext h
      exact spectrumSuspendedCylinderComposite_step X Y Z n a h

end SerrePositivity.KST.SConstruction
