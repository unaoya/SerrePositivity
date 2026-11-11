module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedAttachmentBlockSimplex

/-!
# 元の prefix・残り・refined 全図式と全単体作用素

概要：内部切断を前後の全語へ繋いだ全図式を、元の再添字へ照合する。
方針：接合点の表示を保って元の前後の語と内部三列の整合を連結する。
規約：prefix と残りの動く端点、元の全行・全縦射を保持する。
使われ方：hammock の分割の単体的自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n m : SimplexCategoryᵒᵖ}
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) (i : Fin w.length)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ []) (θ : n ⟶ m)
  (hθ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ).obj 0) i ≠ [])

lemma prefixDiagram_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_endpoints rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.sourceJoint_simplex W τ i θ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorSource_simplex W τ i h θ hθ) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.beforeDiagram_simplex W τ i θ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.leftBlock_simplex W τ i h θ hθ)

lemma residualDiagram_simplex :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_precomp]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_endpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorTarget_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.targetJoint_simplex W τ i θ) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rightBlock_simplex W τ i h θ hθ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.afterDiagram_simplex W τ i θ)

lemma refinedDiagram_simplex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedDiagram W τ i h).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ) := by
  apply eq_of_heq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_endpoints rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorTarget_simplex W τ i h θ hθ) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_heq_endpoints rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorSource_simplex W τ i h θ hθ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorTarget_simplex W τ i h θ hθ) (prefixDiagram_simplex W τ i h θ hθ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generatorBlock_simplex W τ i h θ hθ)) (residualDiagram_simplex W τ i h θ hθ)

lemma refinedFunctor_simplex :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).map θ τ) i hθ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowIndex θ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.refinedFunctor W τ i h :=
  congrArg (fun F => F.fixedFunctor) (refinedDiagram_simplex W τ i h θ hθ)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
