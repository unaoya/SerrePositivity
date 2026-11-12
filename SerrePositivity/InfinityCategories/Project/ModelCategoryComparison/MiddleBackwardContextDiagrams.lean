module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramParts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramOfFunctor
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily

/-!
# 任意の前後の語を保持した中央列の置換図式

概要：元の全体の zigzag 圏から局所ブロックを抽出し、左右の置換図式を貼る。
方針：前後の語を元の図式から切り出し、動く接合対象で局所図式と連結する。
規約：全体の端点だけを固定する。元の全体との再構成の照合は別に証明する。
使われ方：任意の前後の語の中の backward 挿入の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n m : ℕ) (X Y : C)

abbrev wholeWord := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m)) b

def originalDiagram := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ofFunctor
  (𝟭 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y))

def prefixDiagram := (originalDiagram a b n m X Y).leftPart.leftPart

def coreDiagram := (originalDiagram a b n m X Y).leftPart.rightPart

def suffixDiagram := (originalDiagram a b n m X Y).rightPart

def coreFamily := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardMovingExtractFamily.family (coreDiagram a b n m X Y)

def rebuiltDiagram := ((prefixDiagram a b n m X Y).append
  (coreFamily a b n m X Y).movingDiagram).append (suffixDiagram a b n m X Y)

def rebuiltFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y :=
  (rebuiltDiagram a b n m X Y).fixedFunctor

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

def pullbackDiagram := ((prefixDiagram a b n m X Y).append
  ((coreFamily a b n m X Y).pullbackDiagram cof)).append (suffixDiagram a b n m X Y)

def pullbackFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y :=
  (pullbackDiagram a b n m X Y cof).fixedFunctor

def pullbackCounit : pullbackFunctor a b n m X Y cof ⟶ rebuiltFunctor a b n m X Y :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (prefixDiagram a b n m X Y)).append
    ((coreFamily a b n m X Y).pullbackCounit cof)).append
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (suffixDiagram a b n m X Y))).natTrans

variable (hc : ∀ S, trivialCofibrations C ((coreFamily a b n m X Y).middle.app S))

def pushoutDiagram := ((prefixDiagram a b n m X Y).append
  ((coreFamily a b n m X Y).pushoutDiagram hc)).append (suffixDiagram a b n m X Y)

def pushoutFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y ⥤
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (wholeWord a b n m) X Y :=
  (pushoutDiagram a b n m X Y hc).fixedFunctor

def pushoutUnit : rebuiltFunctor a b n m X Y ⟶ pushoutFunctor a b n m X Y hc :=
  (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (prefixDiagram a b n m X Y)).append
    ((coreFamily a b n m X Y).pushoutUnit hc)).append
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramHom.Hom.id (suffixDiagram a b n m X Y))).natTrans

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardContextDiagrams
