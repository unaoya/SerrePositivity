module

public import SerrePositivity.KST.Spectra.CosimplicialTerminalMatching
public import SerrePositivity.KST.Spectra.PostMappingFibration

/-!
概要：点つき固定源からの内部 Hom は、余単体図式の Reedy Kan 条件を保つ。
方針：matching 射と極限保存の arrow 同型で移し、点つき内部 Hom の fibration 保存を使う。
規約：源に Kan 性を要求しない。loop の場合を含む。
使われ方：Goerss–Jardine VII §4、BF 1978 §2。Ω 図式の Reedy 置換の随伴構造。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.Reedy
namespace SerrePositivity.KST.Spectra.CosimplicialCotensorReedyKan
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 点つき固定源からの内部 Hom は実際の余単体 Reedy Kan 条件を保つ。 -/
lemma reedyTerminal (A : PointedSimplicialSet.{u})
    (X : CosimplicialObject PointedSimplicialSet.{u})
    (hX : reedyRight simplex J.rlp (terminal.from (X ⋙ PointedSimplicialSet.forget))) :
    reedyRight simplex J.rlp
      (terminal.from ((X ⋙ ihom A) ⋙ PointedSimplicialSet.forget)) := by
  have hm (j : SimplexCategory) :
      J.rlp (((matchingComparison simplex j).app X).right) := by
    have hraw := (J.rlp.arrow_iso_iff
      (CosimplicialTerminalMatching.arrowIso (X ⋙ PointedSimplicialSet.forget) j)).mp (hX j)
    exact (J.rlp.arrow_iso_iff
      (CosimplicialMatchingFunctor.arrowIso PointedSimplicialSet.forget X j)).mpr hraw
  intro j
  apply (J.rlp.arrow_iso_iff (CosimplicialTerminalMatching.arrowIso
    ((X ⋙ ihom A) ⋙ PointedSimplicialSet.forget) j)).mpr
  apply (J.rlp.arrow_iso_iff (CosimplicialMatchingFunctor.arrowIso
    ((ihom A) ⋙ PointedSimplicialSet.forget) X j)).mp
  let : Fibration (((matchingComparison simplex j).app X).right) :=
    (modelCategoryQuillen.fibration_iff _).mpr (hm j)
  have h := PointedMapping.post_fibration A ((matchingComparison simplex j).app X)
  exact (modelCategoryQuillen.fibration_iff _).mp h

end
end SerrePositivity.KST.Spectra.CosimplicialCotensorReedyKan
