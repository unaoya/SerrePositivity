module

public import SerrePositivity.KST.Spectra.ReplacedTotalization

/-!
概要：元から Reedy Kan な点つき図式の通常の Tot と置換後の Tot の比較。
方針：自然な置換の単位の各段の π_* 同型を通常の Tot の不変性へ渡す。
規約：比較は既に構成した実際の標準射であり、任意に選んだ同型ではない。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot と置換した Tot の π_* 比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.PointedTotalization

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：Reedy Kan な点つき図式の Tot から置換した Tot への標準射は全基点 π_* 同型。
方針：置換の単位の各段の同型性と通常の Tot のホモトピー不変性を使う。
規約：元の図式の終射の相対 matching 条件を明示する。
使われ方：Goerss–Jardine VIII §1。通常の Tot の自然な置換比較。 -/
lemma replacementUnit_piIsomorphism
    (X : CosimplicialObject PointedSimplicialSet.{u})
    [∀ j, KanComplex (X.obj j).right] [KanComplex (obj X).right]
    (hX : reedyRight simplex SSet.modelCategoryQuillen.J.rlp
      (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (obj X).right) (Y := (replacementObj X).right)
      (replacementUnit.app X).right := by
  let : ∀ j, KanComplex ((PointedCosimplicialKanReplacement.obj X).obj j).right :=
    fun j ↦ PointedCosimplicialKanReplacement.kanComplex X j
  let : KanComplex (obj (PointedCosimplicialKanReplacement.obj X)).right :=
    inferInstanceAs (KanComplex (replacementObj X).right)
  exact map_piIsomorphism (PointedCosimplicialKanReplacement.unitApp X) hX
    (CosimplicialKanReplacement.terminal_rlp (X ⋙ PointedSimplicialSet.forget))
    (PointedCosimplicialKanReplacement.unit_piIsomorphism X)

end

end SerrePositivity.KST.Spectra.PointedTotalization
