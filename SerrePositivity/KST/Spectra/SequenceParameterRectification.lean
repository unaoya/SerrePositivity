module

public import SerrePositivity.KST.Spectra.RawSpectrumHomPoints
public import SerrePositivity.KST.Spectra.PointedHomTransposeComponents
public import SerrePositivity.KST.Spectra.SequenceHomotopyRectification
public import SerrePositivity.KST.Spectra.RawSpectrumCotensorIso

/-!
概要：全点つきパラメータの段の族を、元の全 Hom に値を取る厳密な整合族へ直す。
方針：パラメータを標的の内部 Hom へ転置し、列を厳密化して元の交換同型で戻す。
規約：パラメータの全体を同時に保持。使われ方：loop の全 Hom 比較の列方向の組み立て。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (A : PointedSimplicialSet.{u})
    (f : ∀ n, (X.level n).space ⟶ (ihom A).obj (Y.level n).space)
    (hf : ∀ n, PointedMapping.componentOf
        (PointedSimplicialSet.circle.{u} ◁ f n ≫ (KanSequence.mapping A Y).sigma n) =
      PointedMapping.componentOf (X.sigma n ≫ f (n + 1)))

/-- パラメータ全体を内部 Hom へ移して厳密化した、元の列の厳密な比較。 -/
def rectifiedParameterHom : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y) :=
  KanSequence.rectify (X := X.toKanSequence) (Y := KanSequence.mapping A Y) X.sigma_mono f hf

/-- 厳密化した全パラメータ族を、元の同じ全 Hom 内に表示する。 -/
def rectifyParameter : A ⟶ pointedSpace X Y :=
  uncurry' (homPoint X (KanSequence.mapping A Y) (rectifiedParameterHom X Y A f hf) ≫
    cotensorComparison X Y A)

/-- 厳密化した族の段座標は、同じ修正済み段射の転置。 -/
lemma rectifyParameter_evaluation (n : ℕ) :
    rectifyParameter X Y A f hf ≫ pointedEvaluation X Y n =
      PointedMapping.transpose ((rectifiedParameterHom X Y A f hf).app n) := by
  apply curry'_injective
  rw [← curry'_ihom_map, rectifyParameter, curry'_uncurry', Category.assoc,
    cotensorComparison_evaluation]
  dsimp only [exchangeFamily]
  rw [← Category.assoc, homPoint_evaluation]
  exact _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeVertices.curry'_hom _

/-- 全パラメータの修正後の座標は、元の指定した全パラメータの座標と同じ成分。 -/
lemma rectifyParameter_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (rectifyParameter X Y A f hf ≫ pointedEvaluation X Y n) =
      PointedMapping.componentOf (PointedMapping.transpose (f n)) := by
  rw [rectifyParameter_evaluation]
  apply PointedMapping.componentOf_transpose
  exact KanSequence.rectify_component (X := X.toKanSequence)
    (Y := KanSequence.mapping A Y) X.sigma_mono f hf n

/-- 各段の修正は、元のパラメータ全体の基点を固定する実際のホモトピーで比較できる。 -/
lemma rectifyParameter_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (rectifyParameter X Y A f hf ≫ pointedEvaluation X Y n).right
        (PointedMapping.transpose (f n)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom (X.level n).space (Y.level n).space).hom := by
  let parameterTargetKan :
      KanComplex (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1
    (rectifyParameter_evaluation_component X Y A f hf n)

/-- 元の零段の全パラメータの座標は、厳密化で変更しない。 -/
lemma rectifyParameter_evaluation_zero :
    rectifyParameter X Y A f hf ≫ pointedEvaluation X Y 0 = PointedMapping.transpose (f 0) := by
  rw [rectifyParameter_evaluation]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
