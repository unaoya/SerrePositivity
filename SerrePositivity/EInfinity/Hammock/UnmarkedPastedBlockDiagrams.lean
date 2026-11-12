module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedAfterData
public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedJoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagEndpointHExt

/-!
# 元の貼り戻しの前後の全図式の端点表示を含む回収

概要：元の before/after を元の prefix・残りの全図式へ異種等式で照合する。
方針：元の語・接合点関手・全頂点・全横列・全縦成分の回収を外延性へ渡す。
規約：端点表示以外の元の全データを保持する。
使われ方：実際の指定 prefix と残りの hammock の点の回収。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.Index W)
  (σ : (AllMarked.nativeGraph W X g.val.left a).obj n)
  (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths b g.val.right Y).obj n)

lemma before_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (before_word a b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor ((AllMarked.graphMap W X g.val.left a).app n σ)) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.beforeDiagram W (simplex W g σ τ) (columnIndex a b)
  have hB := sourceJoint_eq W g σ τ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.hext_endpoints rfl hB
  · intro d
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints rfl (congrArg (fun G => G.obj d) hB)
    · intro j
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_vertex (before_word a b) F d j j rfl).trans
        (before_vertex W g σ τ d j)
    · intro j
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (before_word a b) F d j j rfl).trans
        (before_arrow W g σ τ d j)
  · intro d e f j
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (before_word a b) F f j j rfl).trans
      (before_map_app W g σ τ f j)

lemma after_diagram :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord (after_word a b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor τ) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachments.afterDiagram W (simplex W g σ τ) (columnIndex a b)
  have hA := targetJoint_eq W g σ τ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram.hext_endpoints hA rfl
  · intro d
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.object_hext_endpoints (congrArg (fun G => G.obj d) hA) rfl
    · intro j
      let j' := Fin.cast (congrArg (fun w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => w.length + 1) (after_word a b)).symm j
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_vertex (after_word a b) F d j' j rfl).trans
        (after_vertex W g σ τ d j')
    · intro j
      let j' := Fin.cast (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.length (after_word a b)).symm j
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_arrow_heq (after_word a b) F d j' j rfl).trans
        (after_arrow W g σ τ d j')
  · intro d e f j
    let j' := Fin.cast (congrArg (fun w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word => w.length + 1) (after_word a b)).symm j
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.changeWord_map_app_heq (after_word a b) F f j' j rfl).trans
      (after_map_app W g σ τ f j')

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.Pasted
