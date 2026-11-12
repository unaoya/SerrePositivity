module

public import SerrePositivity.KST.Spectra.PointedStandardEndComparison
public import SerrePositivity.KST.Spectra.KanSequenceHomotopyLimit
public import SerrePositivity.KST.Spectra.PointedWeightedEndCotensorWeight

/-!
概要：標準単体の重みの通常 Tot を段とする Kan 列の構成。
方針：Reedy 条件で各段を Kan とし、元の随伴構造射を end と loop 交換へ送る。
規約：構造射は通常の end の構成そのもの。Ω 条件は別に証明する。
使われ方：Goerss–Jardine VIII §1、BF 1978 §2。通常 Tot のスペクトル化への入力。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.KanSequence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 余単体 Kan 列の各スペクトル次数に対する実際の Reedy 条件。 -/
abbrev TotalizationReedy (D : CosimplicialObject KanSequence.{u}) : Prop :=
  ∀ n, reedyRight simplex modelCategoryQuillen.J.rlp
    (terminal.from (D ⋙ levelEvaluation n ⋙ PointedSimplicialSet.forget))

/-- 標準単体 end の通常 Tot の随伴構造射。 -/
def totalizationAdjoint (D : CosimplicialObject KanSequence.{u}) (n : ℕ) :
    PointedWeightedEnd.obj (AsSmall.down ⋙ stdSimplex)
      (levelDiagram (AsSmall.down ⋙ D) n) ⟶
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (PointedWeightedEnd.obj (AsSmall.down ⋙ stdSimplex)
      (levelDiagram (AsSmall.down ⋙ D) (n + 1))) :=
  PointedWeightedEnd.map (AsSmall.down ⋙ stdSimplex)
      (adjointTransformation (AsSmall.down ⋙ D) n) ≫
    (PointedWeightedEnd.cotensorIso PointedSimplicialSet.circle.{u}
      (AsSmall.down ⋙ stdSimplex) (levelDiagram (AsSmall.down ⋙ D) (n + 1))).inv

/-- 通常 Tot の標準単体 end を各段に持つ実際の Kan 列。 -/
def ordinaryTotalization (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) : KanSequence.{u} where
  level n := {
    space := PointedWeightedEnd.obj (AsSmall.down ⋙ stdSimplex)
      (levelDiagram (AsSmall.down ⋙ D) n)
    kan := PointedTotalization.standardEnd_kanComplex (D ⋙ levelEvaluation n) (hD n) }
  sigma n := uncurry (totalizationAdjoint D n)

/-- 標準単体 end の随伴は定義した随伴構造射と一致する。 -/
lemma ordinaryTotalization_adjoint (D : CosimplicialObject KanSequence.{u})
    (hD : TotalizationReedy D) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv ((ordinaryTotalization D hD).level n).space
      ((ordinaryTotalization D hD).level (n + 1)).space
        ((ordinaryTotalization D hD).sigma n) = totalizationAdjoint D n :=
  curry_uncurry _

end
end SerrePositivity.KST.Spectra.KanSequence
