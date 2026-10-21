module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedSimplex
public import SerrePositivity.EInfinity.SimplicialLocalization.GeneratorWordFixedCutLength

/-!
# 元の貼り戻しの一文字の列の全行の切断の前後の長さ

概要：元の三因子を貼った生成列の raw な射列は長さ一で、全行の切断の前後は長さ零である。
方針：元の左右の列への任意の射の性質の移送と FixedCut の因子化を使う。
規約：消去後の長さだけでなく元の射列自身の長さを使う。
使われ方：元の prefix・残りの点を恒等列の挿入へ照合する。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : FactorTarget.Index W)

lemma column_length_one (S : Zigzag W.paths a X g.val.left)
    (T : Zigzag W.paths b g.val.right Y) : ((obj W g S T).arrow (columnIndex a b)).length = 1 := by
  let L : MorphismProperty (Paths C) := fun _ _ p => p.length = 1
  exact ((ZigzagAppend.arrow_left_property L _ _ _).trans
    (ZigzagAppend.arrow_right_property L S
      (ForwardZigzag.obj (W := W.paths) g.val.hom.toPath) (0 : Fin 1))).2 rfl

variable (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (graph W.paths b g.val.right Y).obj n)
  (h : ∃ j, column W ((simplex W g σ τ).obj 0) j ≠ [])

lemma selected_column_length_one (d : Fin (n.unop.len + 1)) :
    (((simplex W g σ τ).obj d).arrow (AttachedPrefix.index W (simplex W g σ τ) h)).length = 1 :=
  (congrArg (fun j => (((simplex W g σ τ).obj d).arrow j).length)
    (simplex_firstColumn W g σ τ h)).trans
      (column_length_one W g (((AllMarked.graphMap W X g.val.left a).app n σ).obj d) (τ.obj d))

lemma cut_left_length_zero (d : Fin (n.unop.len + 1)) :
    (fixedRowCut W (simplex W g σ τ) (AttachedPrefix.index W (simplex W g σ τ) h)
      (AttachedPrefix.nonempty W _ h) d).left.length = 0 :=
  GeneratorWord.FixedCut.left_length_of_one W _ (selected_column_length_one W g σ τ h d)

lemma cut_right_length_zero (d : Fin (n.unop.len + 1)) :
    (fixedRowCut W (simplex W g σ τ) (AttachedPrefix.index W (simplex W g σ τ) h)
      (AttachedPrefix.nonempty W _ h) d).right.length = 0 :=
  GeneratorWord.FixedCut.right_length_of_one W _ (selected_column_length_one W g σ τ h d)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
