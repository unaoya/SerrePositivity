module
public import SerrePositivity.KST.SConstruction.BoundaryRealizationInvariance
public import SerrePositivity.KST.SConstruction.KHomotopyFunctor
public import SerrePositivity.KST.Spectra.SpectrumHomotopyEquivalences

/-! # 元の正反復実現から実 BF K 射の全整数 π_* 同型へ
概要：実現の同値不変性を、構成済みの実 BF K 射の全整数次数へ渡す。
方針：元の Kan 列の各段で検査し、単射置換の自然な π 比較を打ち消す。
規約：Sp 値の coherent 関手性の完成とは区別する。使われ方：K-4d の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.SimplicialModel
variable {X Y : StableModel.{u}} (f : X ⟶ Y)
  (hf : ∀ r : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
    ((multiRealizationFunctor (r + 1)).map f)))
include hf

/-- 元の K 候補列の全段の元の射は、全基点の π_* 同型。 -/
lemma kKanSequenceLevelMap_piIsomorphism (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (kKanSequenceLevelMap f r).right := by
  cases r with
  | zero => exact boundaryKSpaceMap_piIsomorphism f (hf 0)
  | succ r => exact boundaryKanRealizationMap_piIsomorphism f r (hf r)

/-- 元の K 候補列の全段・全自然数次数のホモトピー集合で、元の射は可逆。 -/
lemma rawKStageHomotopy_map_isIso (r n : ℕ) :
    IsIso ((rawKStageHomotopyFunctor r n).map f) := by
  let g := kKanSequenceLevelMap f r
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism n g.right
    (kKanSequenceLevelMap_piIsomorphism f hf r) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint g)
  have he : (rawKStageHomotopyFunctor r n).map f = e.toIso.hom := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfPiIsomorphism_apply n g.right
      (kKanSequenceLevelMap_piIsomorphism f hf r) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint g) a).symm
  rw [he]
  infer_instance

/-- 単射置換した実 K 列の元の射も、全段・全自然数次数で可逆。 -/
lemma kStageHomotopy_map_isIso (r n : ℕ) :
    IsIso ((kStageHomotopyFunctor r n).map f) :=
  (NatIso.isIso_map_iff (kStageHomotopyIso r n) f).mpr (rawKStageHomotopy_map_isIso f hf r n)

/-- 元の実 BF K 射は全整数次数の π_* 同型。 -/
lemma kSpectrumMap_piIsomorphism_of_realization : OmegaSpectrum.PiIsomorphism (kSpectrumMap f) := by
  intro j
  let r := OmegaSpectrum.canonicalLevel j
  let n := OmegaSpectrum.degree j r
  have hb : Function.Bijective (pointedHomotopyMap n ((monicKKanSequenceMap f).app r)) :=
    (CategoryTheory.isIso_iff_bijective _).mp (kStageHomotopy_map_isIso f hf r n)
  have he : (fun a : OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) j =>
      OmegaSpectrum.homotopyMap (kSpectrumMap f) j a) =
      pointedHomotopyMap n ((monicKKanSequenceMap f).app r) := by
    funext a
    rw [OmegaSpectrum.homotopyMap_apply]
    rfl
  exact Eq.mp (congrArg Function.Bijective he.symm) hb

omit hf in
/-- 完全な逆を保持する安定入力の同値は、元の実 BF K 射で全整数 π_* 同型を誘導する。 -/
lemma kSpectrumMap_piIsomorphism_of_equivalence (e : StableModelEquivalence X Y) :
    OmegaSpectrum.PiIsomorphism (kSpectrumMap e.hom) :=
  kSpectrumMap_piIsomorphism_of_realization e.hom
    (fun r => multiRealization_map_localized_isIso_of_equivalence r e)

end SerrePositivity.KST.SConstruction
