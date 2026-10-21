module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSimplex

/-!
# 任意の三因子の元の標準射による貼り戻しの表示

概要：元の標準射の三因子の貼り戻しを同じ連結単体の標準射へ照合する。
方針：元の包含と二つの元の合成の標準射の回収式を使う。
規約：元の prefix・生成矢・残り・全縦射を保持する。
使われ方：各次数の共同全射性から任意の因子の回収へ移る。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)

lemma pastePoint_inclusions : FactorTarget.pastePoint W X Y g
    ((AllMarked.nativeInclusion W X g.val.left a).app n σ)
    ((graphInclusion W.paths g.val.right Y b).app n τ) =
      (graphInclusion W.paths X Y (Word.append (Word.append a (Word.single .forward)) b)).app n
        (simplex W g σ τ) := by
  let P := (AllMarked.graphMap W X g.val.left a).app n σ
  let A := arrowSimplex W.paths g.val.hom.toPath n
  have hp := congrArg (fun k => k.app n σ) (AllMarked.nativeInclusion_inclusion W X g.val.left a)
  have hi := composePoint_inclusions W.paths X g.val.left g.val.right a (Word.single .forward) P A
  have ho := composePoint_inclusions W.paths X g.val.right Y (Word.append a (Word.single .forward))
    b (P.prod' A ⋙ ZigzagAppend.functor) τ
  have he := congrArg (fun p => composePoint W.paths X g.val.right Y
    (composePoint W.paths X g.val.left g.val.right p (arrowPoint W.paths g.val.hom.toPath n))
    ((graphInclusion W.paths g.val.right Y b).app n τ)) hp
  have hm := congrArg (fun p => composePoint W.paths X g.val.right Y p
    ((graphInclusion W.paths g.val.right Y b).app n τ)) hi
  exact he.trans (hm.trans ho)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
