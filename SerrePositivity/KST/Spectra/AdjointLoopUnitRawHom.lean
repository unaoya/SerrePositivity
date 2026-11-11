module

public import SerrePositivity.KST.Spectra.AdjointLoopKanSequence
public import SerrePositivity.KST.Spectra.RawSpectrumPostWhitehead
public import SerrePositivity.KST.Spectra.RawSpectrumMappingCompositionLaws

/-!
概要：補助 loop 単位を元の全整合 Hom へ適用する。
方針：厳密な単位の後合成を使い、段ごとの π 同型と豊穣合成の自然性を移す。
規約：nativeLoop への比較と相対 BF 分解はここでは主張しない。
使われ方：相対 BF 置換の前後で、単位と全 Hom パラメータを保持する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 概要：補助 loop 単位による元の Raw Hom の後合成。
方針：全整合写像の既存の後合成へ厳密単位を代入する。
規約：源は任意の BF 対象、標的は元の Kan 列。
使われ方：単位の全 Hom 上の比較。 -/
def adjointLoopUnitPost (A : OmegaSpectrum.{u}) (X : KanSequence.{u}) :
    space A X ⟶ space A (KanSequence.adjointLoop (KanSequence.tail X)) :=
  post A (KanSequence.adjointLoopTailUnit X)

/-- 概要：全 Hom の単位を各段で評価すると、元の構造随伴の後合成となる。
方針：元の全整合後合成の評価式を使う。
規約：全単体上の厳密等式。
使われ方：相対分解の端点の照合。 -/
@[reassoc] lemma adjointLoopUnitPost_evaluation
    (A : OmegaSpectrum.{u}) (X : KanSequence.{u}) (n : ℕ) :
    adjointLoopUnitPost A X ≫
      evaluation A (KanSequence.adjointLoop (KanSequence.tail X)) n =
    evaluation A X n ≫
      (PointedObject.basedHomMap (A.level n).space
        (KanSequence.ordinaryStructureAdjoint X n)).right :=
  post_evaluation A (KanSequence.adjointLoopTailUnit X) n

/-- 概要：Ω 条件のある列の単位は元の全 Raw Hom 上でも全基点 π 同型。
方針：各段の元の構造随伴の π 同型へ全 Hom の Whitehead 比較を使う。
規約：相対分解や nativeLoop 比較を仮定しない。
使われ方：単位の同値性を全 Hom へ移す。 -/
lemma adjointLoopUnitPost_piIsomorphism (A : OmegaSpectrum.{u})
    (X : KanSequence.{u}) (hX : X.OmegaCondition) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (adjointLoopUnitPost A X) :=
  pointedPost_levelwise_piIsomorphism A (KanSequence.adjointLoopTailUnit X)
    (KanSequence.adjointLoopTailUnit_levelwise hX)

/-- 概要：単位の全 Hom 後合成は標的列の厳密射に対して自然。
方針：元の単位の厳密自然性を後合成の合成則で写す。
規約：零単体だけでなく全単体集合の射の等式。
使われ方：相対 BF 比較の標的変数を保持する。 -/
lemma adjointLoopUnitPost_natural (A : OmegaSpectrum.{u})
    {X Y : KanSequence.{u}} (f : X ⟶ Y) :
    post A f ≫ adjointLoopUnitPost A Y =
      adjointLoopUnitPost A X ≫
        post A (KanSequence.adjointLoopMap (KanSequence.tailHom f)) := by
  rw [adjointLoopUnitPost, adjointLoopUnitPost, ← post_comp, ← post_comp]
  exact congrArg (post A) (KanSequence.adjointLoopTailUnit_natural f)

/-- 概要：単位の後合成は源の元の豊穣 Hom の全パラメータと厳密に可換。
方針：全整合合成と後合成の厳密交換則を適用する。
規約：源の射を頂点やホモトピー類に制限しない。
使われ方：相対 BF 置換で保持する源の全 Hom 自然性。 -/
lemma adjointLoopUnitPost_composition (A B : OmegaSpectrum.{u})
    (X : KanSequence.{u}) :
    composition A B X ≫ adjointLoopUnitPost A X =
      (𝟙 (OmegaSpectrum.mappingSpace A B) ⊗ₘ adjointLoopUnitPost B X) ≫
        composition A B (KanSequence.adjointLoop (KanSequence.tail X)) :=
  composition_post A B (KanSequence.adjointLoopTailUnit X)

end SerrePositivity.KST.Spectra.RawSpectrumMapping
