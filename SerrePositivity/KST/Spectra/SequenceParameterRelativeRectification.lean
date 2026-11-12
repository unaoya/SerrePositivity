module

public import SerrePositivity.KST.Spectra.SequenceRelativeRectification
public import SerrePositivity.KST.Spectra.RawSpectrumParameterHomFamilies

/-!
概要：指定した点つき部分パラメータの元の全 Hom 族を厳密に保つ、全列の相対厳密化。
方針：源の制限の Kan fibration に沿って垂直な修正鎖を反復し、元の cotensor 交換で戻す。
規約：垂直な構造比較鎖を入力する。使われ方：loop の元の全 Hom 比較の相対構成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 部分パラメータへの制限は、各段で実際のホーンへの RLP を持つ。 -/
lemma mappingPre_level_horn_rlp {A B : PointedSimplicialSet.{u}} (j : B ⟶ A) [Mono j.right]
    (Y : KanSequence.{u}) (n : ℕ) :
    SSet.modelCategoryQuillen.J.rlp ((KanSequence.mappingPre j Y).app n).right :=
  (SSet.modelCategoryQuillen.fibration_iff _).1
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_fibration j (Y.level n).space)

variable (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A B : PointedSimplicialSet.{u}}
  (j : B ⟶ A) [Mono j.right] (c : B ⟶ pointedSpace X Y)
  (f : ∀ n, (X.level n).space ⟶ (ihom A).obj (Y.level n).space)
  (hb : ∀ n, f n ≫ (KanSequence.mappingPre j Y).app n =
    (homOfParameterFamily X Y B c).app n)
  (hf : ∀ n, PointedMapping.VerticalChain ((KanSequence.mappingPre j Y).app (n + 1))
    (X.sigma n ≫ f (n + 1))
    (PointedSimplicialSet.circle.{u} ◁ f n ≫ (KanSequence.mapping A Y).sigma n))

/-- 指定部分上の元の族を厳密に保って構成した、全パラメータの厳密な列射。 -/
def relativeParameterHom : KanSequence.Hom X.toKanSequence (KanSequence.mapping A Y) :=
  KanSequence.relativeRectify (X := X.toKanSequence) X.sigma_mono
    (KanSequence.mappingPre j Y) (mappingPre_level_horn_rlp j Y)
    (homOfParameterFamily X Y B c) f hb hf

/-- 元の指定部分の列射への射影は、修正後も各段で厳密に保持する。 -/
lemma relativeParameterHom_projection (n : ℕ) :
    (relativeParameterHom X Y j c f hb hf).app n ≫ (KanSequence.mappingPre j Y).app n =
      (homOfParameterFamily X Y B c).app n :=
  KanSequence.relativeRectify_projection (X := X.toKanSequence) X.sigma_mono
    (KanSequence.mappingPre j Y) (mappingPre_level_horn_rlp j Y)
    (homOfParameterFamily X Y B c) f hb hf n

/-- 各段の修正鎖は、指定部分への元の制限を全区間で固定する。 -/
lemma relativeParameterHom_chain (n : ℕ) :
    PointedMapping.VerticalChain ((KanSequence.mappingPre j Y).app n) (f n)
      ((relativeParameterHom X Y j c f hb hf).app n) :=
  KanSequence.relativeRectify_chain (X := X.toKanSequence) X.sigma_mono
    (KanSequence.mappingPre j Y) (mappingPre_level_horn_rlp j Y)
    (homOfParameterFamily X Y B c) f hb hf n

/-- 指定部分上の族を保持する、元の全 Hom への相対厳密化。 -/
def rectifyParameterRelative : A ⟶ pointedSpace X Y :=
  parameterFamily X Y A (relativeParameterHom X Y j c f hb hf)

/-- 相対厳密化した族の元の段評価は、同じ修正済み段射の転置。 -/
lemma rectifyParameterRelative_evaluation (n : ℕ) :
    rectifyParameterRelative X Y j c f hb hf ≫ pointedEvaluation X Y n =
      PointedMapping.transpose ((relativeParameterHom X Y j c f hb hf).app n) :=
  parameterFamily_evaluation X Y A (relativeParameterHom X Y j c f hb hf) n

/-- 元の指定された部分パラメータの族を、全列・全単体で厳密に保持する。 -/
lemma rectifyParameterRelative_boundary : j ≫ rectifyParameterRelative X Y j c f hb hf = c := by
  apply pointed_hom_ext X Y
  intro n
  rw [Category.assoc, rectifyParameterRelative_evaluation]
  have hp := relativeParameterHom_projection X Y j c f hb hf n
  have he := (PointedMapping.transpose_pre_inner
    ((relativeParameterHom X Y j c f hb hf).app n) j).symm
  exact he.trans ((congrArg PointedMapping.transpose hp).trans
    (homOfParameterFamily_transpose_evaluation X Y B c n))

/-- 各段の全パラメータ座標は、元の段射の転置と同じ成分。 -/
lemma rectifyParameterRelative_evaluation_component (n : ℕ) :
    PointedMapping.componentOf (rectifyParameterRelative X Y j c f hb hf ≫
      pointedEvaluation X Y n) = PointedMapping.componentOf (PointedMapping.transpose (f n)) := by
  rw [rectifyParameterRelative_evaluation]
  apply PointedMapping.componentOf_transpose
  exact (relativeParameterHom_chain X Y j c f hb hf n).component.symm

/-- 元の段座標と修正後の段座標は、全パラメータの基点を固定するホモトピーを持つ。 -/
lemma rectifyParameterRelative_evaluation_homotopy (n : ℕ) :
    ∃ H : SSet.Homotopy (rectifyParameterRelative X Y j c f hb hf ≫
        pointedEvaluation X Y n).right (PointedMapping.transpose (f n)).right,
      A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          (PointedObject.basedHom (X.level n).space (Y.level n).space).hom := by
  let coordinateKan :
      KanComplex (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  exact (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).1
    (rectifyParameterRelative_evaluation_component X Y j c f hb hf n)

/-- 相対厳密化でも零段の全パラメータ座標を厳密に保持する。 -/
lemma rectifyParameterRelative_evaluation_zero :
    rectifyParameterRelative X Y j c f hb hf ≫ pointedEvaluation X Y 0 =
      PointedMapping.transpose (f 0) := by
  rw [rectifyParameterRelative_evaluation]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
