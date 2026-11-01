module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedAttachmentBlockSimplex

/-!
# 元の prefix・残り・refined 全図式と全単体作用素

概要：内部切断を前後の全語へ繋いだ全図式を、元の再添字へ照合する。
方針：接合点の表示を保って元の前後の語と内部三列の整合を連結する。
規約：prefix と残りの動く端点、元の全行・全縦射を保持する。
使われ方：hammock の分割の単体的自然性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
open CategoryTheory SimplicialLocalization Zigzag.MovingDiagram

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : column W (((graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma prefixDiagram_simplex :
    HEq (prefixDiagram W ((graph W.paths w X Y).map θ τ) i hθ)
      ((prefixDiagram W τ i h).precomp (rowIndex θ)) := by
  dsimp only [prefixDiagram]
  rw [append_precomp]
  exact append_heq_endpoints rfl (sourceJoint_simplex W τ i θ)
    (generatorSource_simplex W τ i h θ hθ) (beforeDiagram_simplex W τ i θ)
    (leftBlock_simplex W τ i h θ hθ)

lemma residualDiagram_simplex :
    HEq (residualDiagram W ((graph W.paths w X Y).map θ τ) i hθ)
      ((residualDiagram W τ i h).precomp (rowIndex θ)) := by
  dsimp only [residualDiagram]
  rw [append_precomp]
  exact append_heq_endpoints (generatorTarget_simplex W τ i h θ hθ)
    (targetJoint_simplex W τ i θ) rfl (rightBlock_simplex W τ i h θ hθ)
    (afterDiagram_simplex W τ i θ)

lemma refinedDiagram_simplex :
    refinedDiagram W ((graph W.paths w X Y).map θ τ) i hθ =
      (refinedDiagram W τ i h).precomp (rowIndex θ) := by
  apply eq_of_heq
  exact append_heq_endpoints rfl (generatorTarget_simplex W τ i h θ hθ) rfl
    (append_heq_endpoints rfl (generatorSource_simplex W τ i h θ hθ)
      (generatorTarget_simplex W τ i h θ hθ) (prefixDiagram_simplex W τ i h θ hθ)
      (generatorBlock_simplex W τ i h θ hθ)) (residualDiagram_simplex W τ i h θ hθ)

lemma refinedFunctor_simplex :
    refinedFunctor W ((graph W.paths w X Y).map θ τ) i hθ =
      rowIndex θ ⋙ refinedFunctor W τ i h :=
  congrArg (fun F => F.fixedFunctor) (refinedDiagram_simplex W τ i h θ hθ)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Attachments
