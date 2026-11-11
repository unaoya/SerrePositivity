module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeGraph
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# 元の augmentation 正方形の全単体ホモトピー

概要：始域比較の全四列の自然変換を元の要素図式の nerve ホモトピーへ移す。
方針：同じ区間関手に元の全射列を代入する。
規約：異なる Hom 宇宙と元の全成分を保持する。
使われ方：始域比較の anodyne 局所化内の可換式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
open CategoryTheory MonoidalCategory SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type v} [Category.{0} I] {X' X Y : C}
  (A' A : I ⥤ C) (p' : A' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (p : A ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (α : A' ⟶ A) (f : X' ⟶ X) (σ : A ⟶ (Functor.const I).obj Y)
  (h : α ≫ p = p' ≫ (Functor.const I).map f)
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def diagramHomotopyMap : nerve (ULiftHom.{max u v} I) ⊗
    SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word X' Y where
  app _ := ↾fun a =>
    ((SSet.stdSimplex.objEquiv a.2).toOrderHom.monotone.functor.prod'
      (a.1 ⋙ ULiftHom.down.{0, v, max u v})) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramComponent W A p hp f σ hA A' p' hp' α h hA'))
  naturality _ _ _ := rfl

def diagramHomotopy : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramGraphMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA)) where
  h := diagramHomotopyMap W A' A p' hp' p hp α f σ h hA' hA
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j a
    change 𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA).map
        (ULiftHom.down.map (τ.map a)) =
      eqToHom rfl ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA).map
        (ULiftHom.down.map (τ.map a)) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro τ
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro i j a
    change 𝟙 _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA).map (ULiftHom.down.map (τ.map a)) =
      eqToHom rfl ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA).map
        (ULiftHom.down.map (τ.map a)) ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

include h in
lemma diagramColimitMap_component :
    AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA)) =
      AnodyneHomotopy.anodyneQ.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA)) := by
  have he := AnodyneHomotopy.map_homotopy_eq AnodyneHomotopy.anodyneQ
    SSet.anodyneExtensions.Q_inverts (diagramHomotopy W A' A p' hp' p hp α f σ h hA' hA)
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap, Functor.map_comp]
  rw [he]

include h in
lemma diagramColimitMap_sourceComparison :
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A' p' hp' (α ≫ σ) hA')) =
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA)) ≫
        AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y) := by
  have huI : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram W A' A p' hp' α σ hA' hA) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_insert, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap_wordAction]
  have huC : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram W A' A p' hp' α σ hA' hA) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A' p' hp' (α ≫ σ) hA') := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperOriginalDiagram_collapse, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap_wordAction]
  have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) Y := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram_insert, ← CategoryTheory.Functor.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap_wordAction, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramColimitMap_precompose]
  rw [← huC, ← huI, diagramColimitMap_component W A' A p' hp' p hp α f σ h hA' hA,
    hl, Functor.map_comp]

end SerrePositivity.EInfinity.Hammock.LeftRoof.Precompose
