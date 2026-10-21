module

public import SerrePositivity.EInfinity.Hammock.UnmarkedRefinementRecovery
public import SerrePositivity.EInfinity.Hammock.ColimitGraph

/-!
# 元の refined hammock 単体と同じ標準射の回収

概要：元の全図式の回収を、元の hammock graph の単体と余極限の標準射へ移す。
方針：同じ WordAction の nerve と標準余錐の自然性を使う。
規約：元の単体 τ 自身への厳密な回収である。
使われ方：指定 prefix と残りの分解と元の hammock の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization

abbrev refinedWord (w : Word) (i : Fin w.length) : Word :=
  Word.append
    (Word.append (Word.append (Word.ColumnSplit.before w i) (Word.single .forward))
      (Word.single .forward))
    (Word.append (Word.single .forward) (Word.ColumnSplit.after w i))

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ [])

def refinedSimplex : (graph W.paths (refinedWord w i) X Y).obj n := refinedFunctor W τ i h

lemma refinedSimplex_recovery :
    ((graphDiagram W.paths X Y).map (refinementMap W τ i h)).app n
      (refinedSimplex W τ i h) = τ := refinedFunctor_recovery W τ i h

lemma refinedSimplex_inclusion :
    (graphInclusion W.paths X Y (refinedWord w i)).app n (refinedSimplex W τ i h) =
      (graphInclusion W.paths X Y w).app n τ := by
  have hn := congrArg (fun f => f.app n (refinedSimplex W τ i h))
    (graphInclusion_naturality W.paths X Y (refinementMap W τ i h))
  have hr := congrArg
    (fun z : (graph W.paths w X Y).obj n => (graphInclusion W.paths X Y w).app n z)
    (refinedSimplex_recovery W τ i h)
  exact hn.symm.trans hr

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
