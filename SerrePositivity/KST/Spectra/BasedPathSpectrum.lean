module

public import SerrePositivity.KST.Spectra.MappingOmegaSequence
public import SerrePositivity.KST.Spectra.PathSpace
public import SerrePositivity.KST.Spectra.SpectrumZeroObject

/-!
概要：基点付き path の BF スペクトルと、元の対象への実際の fibration。
方針：点つき区間の内部 Hom 列を BF 置換し、終点制限と単位評価を合成する。
規約：射影は元の path の終点評価へ厳密に射影される。使われ方：Sp の loop 四角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.KST.Spectra

/-- 基点付き path 列の厳密な終点射。 -/
def KanSequence.basedPathEndpoint (Y : KanSequence.{u}) :
    KanSequence.Hom (KanSequence.mapping _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} Y) Y :=
  (KanSequence.mappingPre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint Y).comp (KanSequence.mappingUnitEvaluation Y)

namespace OmegaSpectrum

/-- 各段で基点付き path を取り BF 置換した実際のスペクトル。 -/
def basedPath (Y : OmegaSpectrum.{u}) : OmegaSpectrum.{u} := cotensor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y

/-- BF path 模型から元の対象への実際の終点射。 -/
def basedPathProjection (Y : OmegaSpectrum.{u}) : basedPath Y ⟶ Y :=
  let q := (cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).comp
    (KanSequence.basedPathEndpoint Y.toKanSequence)
  ⟨q.app, q.comm⟩

/-- 終点射の各段は BF 射影の後に元の path 評価を施す。 -/
lemma basedPathProjection_app (Y : OmegaSpectrum.{u}) (n : ℕ) :
    (basedPathProjection Y).app n = (cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n ≫
      pathEndpoint (Y.level n).space := rfl

/-- 実際の BF path 終点射は各段で Kan fibration。 -/
instance basedPathProjection_fibration (Y : OmegaSpectrum.{u}) (n : ℕ) :
    Fibration ((basedPathProjection Y).app n).right := by
  have hp := (KanSequence.replacementStage
    (KanSequence.mapping _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.{u} Y.toKanSequence) n).projection_rlp
  have : Fibration ((cotensorProjection _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y).app n).right := by
    apply (fibration_iff _).2
    intro T U i hi
    exact hp i (J_le_monomorphisms _ hi)
  rw [basedPathProjection_app, Under.comp_right]
  infer_instance

end OmegaSpectrum
end SerrePositivity.KST.Spectra
