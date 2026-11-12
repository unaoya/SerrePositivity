module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport
public import SerrePositivity.KST.SConstruction.LocalizedPiComparison
public import SerrePositivity.KST.Spectra.SpectrumIntegerHomotopyDetection
public import SerrePositivity.KST.Spectra.SpectrumZeroObject

/-! # 正の実段の弱可縮性から、整数 π 群と Sp の零頂点へ接続する

Sp の安定性は使わず、元の一点スペクトルへの射と整数 π 同値検出を使う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

local instance zeroPositiveUnitKan : KanComplex (𝟙_ SSet.{u}) :=
  inferInstanceAs (KanComplex (PointedObject.point : PointedSimplicialSet.{u}).right)
local instance zeroPositiveSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

/-- 一点単体集合の、零次を含む全ての元の Kan ホモトピー類は一点。 -/
theorem pointKanHomotopy_subsingleton (n : ℕ) (x : (𝟙_ SSet.{u}) _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (𝟙_ SSet.{u}) n x) := by
  have : ∀ k, Subsingleton ((𝟙_ SSet.{u}).PtSimplex k x) := fun k => ⟨fun a b => by
    apply RelativeMorphism.ext
    exact isTerminalTensorUnit.hom_ext _ _⟩
  cases n <;> dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup] <;> infer_instance

/-- Kan 複体から一点への同じ射の局所化可逆性は、全基点の元の π 類を一点にする。 -/
theorem kanHomotopy_subsingleton_of_toPoint_localized_isIso (Y : SSet.{u}) [KanComplex Y]
    (hY : IsIso (AnodyneHomotopy.anodyneQ.map (toUnit Y))) (n : ℕ) (y : Y _⦋0⦌) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y n y) := by
  have := pointKanHomotopy_subsingleton n ((toUnit Y).app (Opposite.op ⦋0⦌) y)
  exact ((kanPiIsomorphism_of_localized_isIso (toUnit Y) hY) y n).injective.subsingleton

/-- 全正段の同じ一点射が局所化可逆なら、同じスペクトルの全整数 π 群は一点。 -/
theorem spectrum_homotopyGroup_subsingleton_of_positive_toPoint
    (X : OmegaSpectrum.{u})
    (hX : ∀ r : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (((X.level (r + 1)).space).right)))) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup X j) :=
  kanHomotopy_subsingleton_of_toPoint_localized_isIso _ (hX j.natAbs) _ _

/-- 同じ一点スペクトルの全整数 π 群は一点。 -/
theorem spectrumPoint_homotopyGroup_subsingleton (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint.{u} j) :=
  pointKanHomotopy_subsingleton _ _

/-- 全整数群が自明なら、元のスペクトル頂点は同じ一点スペクトルとの実同型により零。 -/
theorem spectrum_isZeroVertex_of_homotopyGroup_subsingleton (X : OmegaSpectrum.{u})
    (hX : ∀ j : ℤ, Subsingleton (OmegaSpectrum.homotopyGroup X j)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) := by
  let f := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.from X
  have hf : OmegaSpectrum.PiIsomorphism f := by
    intro j
    have := hX j
    have := spectrumPoint_homotopyGroup_subsingleton.{u} j
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
  have : IsIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated) :=
    OmegaSpectrum.isInvertible_of_piIsomorphism f hf
  exact OmegaSpectrum.pointZeroVertex.isZero.of_vertexIso
    (asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated)).symm

/-- 全正段の実一点射が局所化可逆なら、同じ元のスペクトル頂点は Sp 内で零。 -/
theorem spectrum_isZeroVertex_of_positive_toPoint (X : OmegaSpectrum.{u})
    (hX : ∀ r : ℕ, IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (((X.level (r + 1)).space).right)))) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) :=
  spectrum_isZeroVertex_of_homotopyGroup_subsingleton X
    (spectrum_homotopyGroup_subsingleton_of_positive_toPoint X hX)

end SerrePositivity.KST.Fibration
