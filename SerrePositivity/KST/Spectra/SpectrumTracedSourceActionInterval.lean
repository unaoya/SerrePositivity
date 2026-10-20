module

public import SerrePositivity.KST.Spectra.TracedOriginalLoopStrictInterval
public import SerrePositivity.KST.Spectra.SignedLoopParameterHom
public import SerrePositivity.KST.Spectra.SequenceStrictIntervalPost

/-!
概要：元の源比較の全列区間を、符号付き loop 列の全パラメータ作用へ移す。
方針：同じ StrictInterval にパラメータ付きの厳密な loop 列射を後合成する。
規約：段ごとの区間から全列を推論しない。使われ方：実評価側の最初の比較ホモトピー。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 元の raw 源比較へ、同じ入力族の全列の符号付き loop 作用を後合成する。 -/
def tracedSourceActionParameterHom :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) :=
  (OmegaSpectrum.tracedOriginalLoopRawComparison X).comp
    (KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ))

/-- 同じ全列作用へ、トレース付き源単位の射影を入力する。 -/
def tracedUnitSourceActionParameterHom :
    KanSequence.Hom X.toKanSequence
      (KanSequence.mapping A (KanSequence.signedLoopTail Y.toKanSequence)) :=
  ((OmegaSpectrum.sequenceHom (OmegaSpectrum.tracedSignedLoopUnit X)).comp
    (OmegaSpectrum.signedLoopProjection X)).comp
      (KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ))

/-- 同じ源区間を全列の作用へ送った、両端固定の実際の全列区間。 -/
def tracedSourceActionStrictInterval :
    KanSequence.StrictInterval (tracedSourceActionParameterHom X Y φ)
      (tracedUnitSourceActionParameterHom X Y φ) :=
  (OmegaSpectrum.tracedOriginalLoopRawStrictInterval X).post
    (KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ))

/-- 元の全 Hom のパラメータ族の間で、同じ全列区間を回収した実ホモトピー。 -/
def tracedSourceActionHomotopy :
    SSet.Homotopy
      (parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
        (tracedSourceActionParameterHom X Y φ)).right
      (parameterFamily X (KanSequence.signedLoopTail Y.toKanSequence) A
        (tracedUnitSourceActionParameterHom X Y φ)).right :=
  strictParameterHomotopy X (KanSequence.signedLoopTail Y.toKanSequence) A
    (tracedSourceActionStrictInterval X Y φ)

/-- 同じ全パラメータのホモトピーは、元の零 Hom の基点を区間全体で固定する。 -/
lemma tracedSourceActionHomotopy_base :
    A.hom ▷ (Δ[1] : SSet.{u}) ≫ (tracedSourceActionHomotopy X Y φ).h =
      CartesianMonoidalCategory.toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
        (pointedSpace X (KanSequence.signedLoopTail Y.toKanSequence)).hom :=
  strictParameterHomotopy_base X (KanSequence.signedLoopTail Y.toKanSequence) A
    (tracedSourceActionStrictInterval X Y φ)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
