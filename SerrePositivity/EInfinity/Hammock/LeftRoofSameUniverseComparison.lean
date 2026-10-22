module

public import SerrePositivity.EInfinity.Hammock.LeftRoofPrecomposeHomotopy
public import SerrePositivity.InfinityCategories.F1B.KanNerveNatTransHomotopy

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
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose.SameUniverse
open CategoryTheory MonoidalCategory SerrePositivity.SimplicialModel
variable {C I : Type u} [Category.{u} C] [Category.{u} I]
  (W : MorphismProperty C) [W.IsMultiplicative] {B E X' X Y : C} {w : Word}

def diagramGraphMap (F : I ⥤ Zigzag W w B E) : nerve I ⟶ graph W w B E := nerveMap F

def diagramColimitMap (F : I ⥤ Zigzag W w B E) : nerve I ⟶ colimitGraph W B E :=
  diagramGraphMap W F ≫ graphInclusion W B E w

lemma diagramColimitMap_wordAction (F : I ⥤ Zigzag W w B E) {w' : Word} (f : w ⟶ w') :
    diagramColimitMap W (F ⋙ WordAction.functor f) = diagramColimitMap W F := by
  have h : diagramGraphMap W (F ⋙ WordAction.functor f) =
      diagramGraphMap W F ≫ (graphDiagram W B E).map f := rfl
  unfold diagramColimitMap
  rw [h, Category.assoc, graphInclusion_naturality]

lemma diagramColimitMap_precompose (F : I ⥤ Zigzag W LeftRoof.word X Y) (f : X' ⟶ X) :
    diagramColimitMap W
      (((Functor.const I).obj (ForwardZigzag.obj (W := W) f)).prod' F ⋙ ZigzagAppend.functor) =
    diagramColimitMap W F ≫ precomposePointMap (arrowMap W f) Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  let Γ := σ ⋙ F
  change (graphInclusion W X' Y preWord).app n
      ((arrowSimplex W f n).prod' Γ ⋙ ZigzagAppend.functor) =
    composePoint W X' X Y (arrowPoint W f n)
      ((graphInclusion W X Y LeftRoof.word).app n Γ)
  exact (composePoint_inclusions W X' X Y (Word.single .forward) LeftRoof.word
    (arrowSimplex W f n) Γ).symm

variable (A' A : I ⥤ C) (p' : A' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (p : A ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (α : A' ⟶ A) (f : X' ⟶ X) (σ : A ⟶ (Functor.const I).obj Y)
  (h : α ≫ p = p' ≫ (Functor.const I).map f)
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def diagramHomotopy : SSet.Homotopy
    (diagramGraphMap W (upperDiagram W A' A p' hp' α σ hA' hA))
    (diagramGraphMap W (lowerDiagram W A p hp f σ hA)) :=
  SerrePositivity.InfinityCategories.F1B.kanNerveNatTransHomotopy
    (diagramComponent W A p hp f σ hA A' p' hp' α h hA')

include h in
lemma diagramColimitMap_component :
    AnodyneHomotopy.anodyneQ.map
      (diagramColimitMap W (upperDiagram W A' A p' hp' α σ hA' hA)) =
    AnodyneHomotopy.anodyneQ.map
      (diagramColimitMap W (lowerDiagram W A p hp f σ hA)) := by
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts (diagramHomotopy W A' A p' hp' p hp α f σ h hA' hA)
  simp only [diagramColimitMap, Functor.map_comp]
  rw [he]

include h in
lemma diagramColimitMap_sourceComparison :
    AnodyneHomotopy.anodyneQ.map (diagramColimitMap W
      (LeftRoof.diagram W A' p' hp' (α ≫ σ) hA')) =
    AnodyneHomotopy.anodyneQ.map (diagramColimitMap W (LeftRoof.diagram W A p hp σ hA)) ≫
      AnodyneHomotopy.anodyneQ.map (precomposePointMap (arrowMap W f) Y) := by
  have huI : diagramColimitMap W (upperDiagram W A' A p' hp' α σ hA' hA) =
      diagramColimitMap W (upperOriginalDiagram W A' A p' hp' α σ hA' hA) := by
    rw [← upperOriginalDiagram_insert, diagramColimitMap_wordAction]
  have huC : diagramColimitMap W (upperOriginalDiagram W A' A p' hp' α σ hA' hA) =
      diagramColimitMap W (LeftRoof.diagram W A' p' hp' (α ≫ σ) hA') := by
    rw [← upperOriginalDiagram_collapse, diagramColimitMap_wordAction]
  have hl : diagramColimitMap W (lowerDiagram W A p hp f σ hA) =
      diagramColimitMap W (LeftRoof.diagram W A p hp σ hA) ≫
        precomposePointMap (arrowMap W f) Y := by
    rw [← lowerDiagram_insert, ← CategoryTheory.Functor.assoc,
      diagramColimitMap_wordAction, diagramColimitMap_precompose]
  rw [← huC, ← huI, diagramColimitMap_component W A' A p' hp' p hp α f σ h hA' hA,
    hl, Functor.map_comp]

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose.SameUniverse
