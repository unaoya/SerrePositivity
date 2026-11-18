module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoofPrecomposeHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopy

/-!
# 元の四列 roof 比較の同じ宇宙の任意添字への全単体入口

概要：圏と Hom が同じ宇宙の添字から元の hammock 余極限へ写し、同じ四列比較を適用する。
方針：元の図式と自然変換の nerve をそのまま使い、元の語の操作と前合成を接続する。
規約：Hom 0 は要求せず、同じ元の graph・余極限・全単体を保持する。
使われ方：実 product comma 圏上の基準射側の全三角形 hR。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.SerrePositivity.SimplicialModel
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative] {B E X' X Y : C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}

def diagramGraphMap (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) : nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w B E := nerveMap F

def diagramColimitMap (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) : nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W B E :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W B E w

lemma diagramColimitMap_wordAction (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w B E) {w' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : w ⟶ w') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W F := by
  have h : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W F ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W B E).map f := rfl
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap
  rw [h, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]

lemma diagramColimitMap_precompose (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word X Y) (f : X' ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W
      (((Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)).prod' F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) =
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let Γ := σ ⋙ F
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X' Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.preWord).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n).prod' Γ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X' X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowPoint W f n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word).app n Γ)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions W X' X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.word
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowSimplex W f n) Γ).symm

variable (A' A : I ⥤ C) (p' : A' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (p : A ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (α : A' ⟶ A) (f : X' ⟶ X) (σ : A ⟶ (Functor.const I).obj Y)
  (h : α ≫ p = p' ≫ (Functor.const I).map f)
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def diagramHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA))
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA)) :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramComponent W A p hp f σ hA A' p' hp' α h hA')

include h in
lemma diagramColimitMap_component :
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA)) =
    AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA)) := by
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramHomotopy W A' A p' hp' p hp α f σ h hA' hA)
  simp only [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap, Functor.map_comp]
  rw [he]

include h in
lemma diagramColimitMap_sourceComparison :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A' p' hp' (α ≫ σ) hA')) =
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA)) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y) := by
  have huI : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram W A' A p' hp' α σ hA' hA) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_insert, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction]
  have huC : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram W A' A p' hp' α σ hA' hA) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A' p' hp' (α ≫ σ) hA') := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_collapse, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction]
  have hl : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram_insert, ← CategoryTheory.Functor.assoc,
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_wordAction, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_precompose]
  rw [← huC, ← huI, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse.diagramColimitMap_component W A' A p' hp' p hp α f σ h hA' hA,
    hl, Functor.map_comp]

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LeftRoof.Precompose.SameUniverse
