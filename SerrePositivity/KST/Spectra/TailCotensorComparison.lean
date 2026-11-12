module

public import SerrePositivity.KST.Spectra.SpectrumTail
public import SerrePositivity.KST.Spectra.SignedLoopComparison
public import SerrePositivity.KST.Spectra.SpectrumWhiteheadEquivalence

/-!
概要：BF cotensor と一段の添字移動の実際の比較。
方針：共通の置換前の内部 Hom 列への射影を、単射構造を持つ源から BF 置換へ持ち上げる。
規約：比較射の各段の全基点 π 同型を証明する。使われ方：native loop の delooping。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- cotensor の後で一段移動した対象から、一段移動の cotensor への実際の射。 -/
def tailCotensorComparison (A : PointedSimplicialSet.{u}) (X : OmegaSpectrum.{u}) :
    tail (cotensor A X) ⟶ cotensor A (tail X) := by
  let q := KanSequence.liftHom
    (X := (tail (cotensor A X)).toKanSequence)
    (W := (cotensor A (tail X)).toKanSequence)
    (Z := KanSequence.mapping A (tail X).toKanSequence)
    (tail (cotensor A X)).sigma_mono (cotensorProjection A (tail X))
    (fun n ↦ (KanSequence.replacementStage
      (KanSequence.mapping A (tail X).toKanSequence) n).projection_rlp)
    (KanSequence.tailHom (cotensorProjection A X))
  exact ⟨q.app, q.comm⟩

/-- 比較は共通の置換前の列への射影を厳密に保つ。 -/
lemma tailCotensorComparison_projection (A : PointedSimplicialSet.{u})
    (X : OmegaSpectrum.{u}) (n : ℕ) :
    (tailCotensorComparison A X).app n ≫ (cotensorProjection A (tail X)).app n =
      (cotensorProjection A X).app (n + 1) :=
  KanSequence.liftHom_fac
    (X := (tail (cotensor A X)).toKanSequence)
    (W := (cotensor A (tail X)).toKanSequence)
    (Z := KanSequence.mapping A (tail X).toKanSequence)
    (tail (cotensor A X)).sigma_mono (cotensorProjection A (tail X))
    (fun n ↦ (KanSequence.replacementStage
      (KanSequence.mapping A (tail X).toKanSequence) n).projection_rlp)
    (KanSequence.tailHom (cotensorProjection A X)) n

/-- 一段移動と cotensor の比較は各段で全基点 π 同型。 -/
lemma tailCotensorComparison_levelwise (A : PointedSimplicialSet.{u})
    (X : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((tailCotensorComparison A X).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := ((cotensorProjection A (tail X)).app n).right) _
    (cotensorProjection_piIsomorphism A (tail X) n)
  have h := congrArg Under.Hom.right (tailCotensorComparison_projection A X n)
  simp only [Under.comp_right] at h
  rw [h]
  exact cotensorProjection_piIsomorphism A X (n + 1)

local instance tailCotensorSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance tailCotensorHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := OmegaSpectrum.mappingSpace_kanComplex X Y

/-- 指定した一段移動と cotensor の比較辺は元の Sp の同値。 -/
lemma tailCotensorComparison_isInvertible (A : PointedSimplicialSet.{u})
    (X : OmegaSpectrum.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (tailCotensorComparison A X)) :=
  SpectrumMappingAcyclic.isInvertible_of_levelwise _ (tailCotensorComparison_levelwise A X)

end SerrePositivity.KST.Spectra.OmegaSpectrum
