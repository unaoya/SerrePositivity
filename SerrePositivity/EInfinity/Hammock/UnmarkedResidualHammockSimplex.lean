module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPrefixHammockSimplex
public import SerrePositivity.EInfinity.Hammock.WordCutFactorColumns

/-!
# 選択した残りの hammock と全単体作用素

概要：最初の非指定列の残りの固定端点関手を、元の再添字へ照合する。
方針：選択位置・生成矢・全図式の既存の異種等式を結合する。
規約：端点の表示を含む全行・全縦射を保持する。
使われ方：依存和の切断射の単体的自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (h : ∃ j, column W (τ.obj 0) j ≠ []) (θ : n ⟶ m)
  (hθ : ∃ j, column W (((graph W.paths w X Y).map θ τ).obj 0) j ≠ [])

lemma residualWord_simplex :
    Word.CutFactor.residualWord w (index W ((graph W.paths w X Y).map θ τ) hθ) =
      Word.CutFactor.residualWord w (index W τ h) :=
  congrArg (Word.CutFactor.residualWord w) (index_simplex W τ h θ hθ)

lemma residualFunctor_simplex :
    HEq (Attachments.residualFunctor W ((graph W.paths w X Y).map θ τ)
      (index W ((graph W.paths w X Y).map θ τ) hθ) (nonempty W _ hθ))
      (rowIndex θ ⋙ Attachments.residualFunctor W τ (index W τ h) (nonempty W τ h)) :=
  Zigzag.MovingDiagram.fixedFunctor_heq (residualWord_simplex W τ h θ hθ)
    (congrArg (fun a : Quiver.Total C => (show Paths C from a.right))
      (generator_simplex W τ h θ hθ)) rfl _ _ (residual_simplex W τ h θ hθ)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AttachedPrefix
