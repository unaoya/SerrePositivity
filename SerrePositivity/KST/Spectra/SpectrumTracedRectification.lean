module

public import SerrePositivity.KST.Spectra.SequenceTracedRectificationTriangles
public import SerrePositivity.KST.Spectra.SpectrumHomotopyRectification

/-!
概要：指定構造区間と延長トレースを保持した Kan 列の厳密化を、実際の BF 射へ持ち上げる。
方針：既存の tracedRectify と cofibrant 置換の全単射 RLP を使う。
規約：成分類から構造区間を選び直さない。使われ方：loop の単位と全 Hom の同じ構造入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (hY : Y.OmegaCondition)
  (f : ∀ n, (X.level n).space ⟶ (Y.level n).space)
  (h : ∀ n, PointedMapping.VerticalPath (PointedObject.toPoint (Y.level (n + 1)).space)
    (X.sigma n ≫ f (n + 1)) (PointedSimplicialSet.circle.{u} ◁ f n ≫ Y.sigma n))

/-- 同じ指定構造区間を使った実際の厳密化を BF 対象へ持ち上げる。 -/
def tracedRectifyInto : X ⟶ Y.cofibrantOmegaSpectrum hY := by
  let g := KanSequence.liftHom (X := X.toKanSequence)
    (W := (Y.cofibrantOmegaSpectrum hY).toKanSequence) (Z := Y) X.sigma_mono
    (Y.cofibrantOmegaProjection hY) (fun n => (Y.replacementStage n).projection_rlp)
    (KanSequence.tracedRectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f h)
  exact { app := g.app, comm := g.comm }

/-- 元の指定区間と延長トレースを持つ列射へ厳密に戻る。 -/
lemma tracedRectifyInto_projection (n : ℕ) :
    (tracedRectifyInto X Y hY f h).app n ≫ (Y.cofibrantOmegaProjection hY).app n =
      (KanSequence.tracedRectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f h).app n :=
  KanSequence.liftHom_fac (X := X.toKanSequence)
    (W := (Y.cofibrantOmegaSpectrum hY).toKanSequence) (Z := Y) X.sigma_mono
    (Y.cofibrantOmegaProjection hY) (fun n => (Y.replacementStage n).projection_rlp)
    (KanSequence.tracedRectify (X := X.toKanSequence) (Y := Y) X.sigma_mono f h) n

/-- 同じ比較区間が全段に保持され、BF 射影後の厳密射への実区間となる。 -/
def tracedRectifyIntoComparison (n : ℕ) :
    PointedMapping.VerticalPath (PointedObject.toPoint (Y.level n).space) (f n)
      ((tracedRectifyInto X Y hY f h).app n ≫ (Y.cofibrantOmegaProjection hY).app n) :=
  (KanSequence.tracedRectifyComparison (X := X.toKanSequence) (Y := Y)
    X.sigma_mono f h n).changeEndpoints rfl
    (tracedRectifyInto_projection X Y hY f h n)

/-- トレースを保持した同じ BF 比較も、全段・全基点の π 同型性を保つ。 -/
lemma tracedRectifyInto_levelwise
    (hpi : ∀ n, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f n).right) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism ((tracedRectifyInto X Y hY f h).app n).right := by
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp
    (g := ((Y.cofibrantOmegaProjection hY).app n).right) _ (Y.replacementProjection_piIsomorphism n)
  have hp := (kanPiIsomorphism_iff_of_homotopy
    (tracedRectifyIntoComparison X Y hY f h n).homotopy).mp (hpi n)
  exact hp

end SerrePositivity.KST.Spectra.OmegaSpectrum
