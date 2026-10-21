module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPaste
public import SerrePositivity.EInfinity.Hammock.UnmarkedRefinedPairing
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPoint

/-!
# 元の一段の切断の貼り戻しによる同じ単体の回収

概要：実際の指定 prefix・同じ生成矢・残りを貼ると元の標準射の像に厳密に戻る。
方針：元の包含・合成の標準射の回収式と元の refined 全図式の回収を使う。
規約：同じ元の単体と全行・全縦射を保持する。
使われ方：全余極限・反復抽出の後の貼り戻しが元の恒等射であること。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ [])

lemma paste_point : (FactorTarget.paste W X Y).app n (point W τ h) =
    (graphInclusion W.paths X Y w).app n τ := by
  let i := AttachedPrefix.index W τ h
  let g := generator W τ h
  let P := AttachedPrefix.functor W τ h
  let A := arrowSimplex W.paths g.val.hom.toPath n
  let R := Attachments.residualFunctor W τ i (AttachedPrefix.nonempty W τ h)
  have hp : (AllMarked.inclusion W X g.val.left).app n (leftPoint W τ h) =
      (graphInclusion W.paths X g.val.left (prefixWord w i)).app n P :=
    congrArg (fun k => k.app n (AttachedPrefix.markedSimplex W τ h))
      (AllMarked.nativeInclusion_inclusion W X g.val.left (prefixWord w i))
  have hi := composePoint_inclusions W.paths X g.val.left g.val.right
    (prefixWord w i) (Word.single .forward) P A
  have ho := composePoint_inclusions W.paths X g.val.right Y
    (Word.append (prefixWord w i) (Word.single .forward)) (residualWord w i)
    (P.prod' A ⋙ ZigzagAppend.functor) R
  have he := congrArg (fun p => composePoint W.paths X g.val.right Y
    (composePoint W.paths X g.val.left g.val.right p (arrowPoint W.paths g.val.hom.toPath n))
    (rightPoint W τ h)) hp
  have hm := congrArg (fun p => composePoint W.paths X g.val.right Y p (rightPoint W τ h)) hi
  have hf := congrArg
    (fun F => (graphInclusion W.paths X Y (Attachments.refinedWord w i)).app n F)
    (Attachments.refinedFunctor_pair W τ i (AttachedPrefix.nonempty W τ h)).symm
  exact he.trans (hm.trans (ho.trans (hf.trans
    (Attachments.refinedSimplex_inclusion W τ i (AttachedPrefix.nonempty W τ h)))))

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor
