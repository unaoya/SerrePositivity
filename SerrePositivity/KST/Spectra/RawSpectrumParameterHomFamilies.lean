module

public import SerrePositivity.KST.Spectra.RawSpectrumHomPointInverse
public import SerrePositivity.KST.Spectra.PointedTransposeRestrictions
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso

/-!
概要：元の全 Hom のパラメータ族と、パラメータを標的内部 Hom に移した厳密な列射の往復。
方針：単位パラメータと列射の対応を元の Hom–cotensor 同型へ合成し、各段を転置で計算。
規約：パラメータの Kan 性不要。使われ方：指定部分の族を保持する相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 内部 Hom に値を取る厳密な列射を、元の全 Hom の全パラメータ族へ戻す。 -/
def parameterFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y)) :
    A ⟶ pointedSpace X Y :=
  uncurry' (homPoint X (KanSequence.mapping A Y) f ≫ cotensorComparison X Y A)

/-- 全パラメータ族の各段の元の座標は、同じ列射の段の転置。 -/
lemma parameterFamily_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (f : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y))
    (n : ℕ) : parameterFamily X Y A f ≫ pointedEvaluation X Y n =
      PointedMapping.transpose (f.app n) := by
  apply curry'_injective
  rw [← curry'_ihom_map, parameterFamily, curry'_uncurry', Category.assoc,
    cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, homPoint_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom _

/-- 元の全 Hom に値を取るパラメータ族を、同じ cotensor 値の厳密な列射へ移す。 -/
def homOfParameterFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (c : A ⟶ pointedSpace X Y) :
    KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y) :=
  homOfPoint X (KanSequence.mapping A Y) (curry' c ≫ cotensorInverse X Y A)

/-- 指定した全パラメータ族は、列射へ移して戻しても元の Hom 内で厳密に一致する。 -/
lemma parameterFamily_homOfParameterFamily (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (c : A ⟶ pointedSpace X Y) :
    parameterFamily X Y A (homOfParameterFamily X Y A c) = c := by
  unfold parameterFamily homOfParameterFamily
  rw [homPoint_homOfPoint, Category.assoc, cotensorInverse_comparison,
    Category.comp_id, uncurry'_curry']

/-- 指定した元の族から回収した厳密な列射の転置座標は、元の同じ段評価。 -/
lemma homOfParameterFamily_transpose_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    (A : PointedSimplicialSet.{u}) (c : A ⟶ pointedSpace X Y) (n : ℕ) :
    PointedMapping.transpose ((homOfParameterFamily X Y A c).app n) =
      c ≫ pointedEvaluation X Y n :=
  (parameterFamily_evaluation X Y A (homOfParameterFamily X Y A c) n).symm.trans
    (congrArg (· ≫ pointedEvaluation X Y n) (parameterFamily_homOfParameterFamily X Y A c))

end SerrePositivity.KST.Spectra.RawSpectrumMapping
