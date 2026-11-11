module

public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedNativeRecovery
public import SerrePositivity.EInfinity.Hammock.UnmarkedPastedInclusion
public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyCutInclusion
public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorPasteValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitPoints

/-!
# 任意の元の三因子の貼り戻し後の全因子の回収

概要：元の指定 prefix・非指定生成矢・残りを貼って切ると元の三因子に戻る。
方針：元の標準射の共同全射性と実際の二因子の点の回収を使う。
規約：語の値だけでなく依存和の元の全点を回収する。
使われ方：反復切断と貼り戻しの逆向きの恒等式。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) (X Y : Paths C)
  {n : SimplexCategoryᵒᵖ}

lemma pasteNonempty_cut_point (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y).obj n) :
    (FirstFactor.nonemptyCut W X Y).app n ((pasteNonempty W X Y).app n s) = s := by
  rcases s with ⟨g, p, r⟩
  obtain ⟨a, σ, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (WideSubcategory W.paths))
      (⟨X⟩ : WideSubcategory W.paths) ⟨g.val.left⟩) n p
  change (AllMarked.nativeInclusion W X g.val.left a).app n σ = p at hp
  cases hp
  obtain ⟨b, τ, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths g.val.right Y) n r
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths g.val.right Y b).app n τ = r at hr
  cases hr
  let P := (AllMarked.nativeInclusion W X g.val.left a).app n σ
  let R := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths g.val.right Y b).app n τ
  let η := Pasted.simplex W g σ τ
  have he := Pasted.pastePoint_inclusions W g σ τ
  have hi : (colimitValue W X Y).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b)).app n
        η) ≠ [] := fun hz => pastePoint_nonempty W X Y g P R
          ((congrArg ((colimitValue W X Y).app n) he).trans hz)
  have hz : (pasteNonempty W X Y).app n ⟨g, P, R⟩ =
      (⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W.paths X Y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward)) b)).app n η, hi⟩ :
          (NonemptyValue.space W X Y).obj n) := Subtype.ext he
  exact (congrArg ((FirstFactor.nonemptyCut W X Y).app n) hz).trans
    ((FirstFactor.nonemptyCut_graphInclusion W η (Pasted.simplex_nonempty W g σ τ) hi).trans
      (Pasted.factor_point W g σ τ (Pasted.simplex_nonempty W g σ τ)))

lemma pasteNonempty_nonemptyCut : pasteNonempty W X Y ≫ FirstFactor.nonemptyCut W X Y =
    𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorTarget.space W X Y) := by
  ext n s
  exact pasteNonempty_cut_point W X Y s

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FactorTarget
