module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismReindex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeReindex

/-!
# 元の混合 coherent 単体の全ての面と退化への自然性

概要：元の前面と最後 Hom の自然性を混合単体の全 Hom へ接続する。
方針：全豊穣関手の外延性と同じ端点正規化を使う。
規約：任意の単体圏の射・全 path・元の図式と時間を保持する。
使われ方：native roof 全三角形の実 slice prism。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
open CategoryTheory SSet MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) {I : Type u} [Category.{u} I]
  (U : I ⥤ C.category) {X Y : C.category} (p : U ⟶ (Functor.const I).obj X)
  (hp : ∀ i, C.weakEquivalences (p.app i)) (σ : U ⟶ (Functor.const I).obj Y)
  (hU : ∀ {i j} (a : i ⟶ j), C.weakEquivalences (U.map a))

lemma simplex_naturality {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (kanHammockNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend α).op (simplex C U p hp σ hU Γ t) =
      simplex C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) := by
  apply EnrichedFunctor.ext SSet (fun i => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.obj_extend
    (frontDiagram C U p Γ t) ((kanHammockSourceFunctor C).obj Y) α i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_reindex (frontDiagram C U p Γ t)
    ((kanHammockSourceFunctor C).obj Y) (lastHom C U p hp σ hU Γ t) α
    (lastHom C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom))
    (lastHom_reindex C U p hp σ hU Γ t α) i j

lemma sliceSimplex_naturality {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y)))).map α.op
        (sliceSimplex C U p hp σ hU Γ t) =
      sliceSimplex C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α) (𝟙 Δ[0]) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm (simplex C U p hp σ hU Γ t)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_naturality, Category.assoc,
    SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg (fun z : (kanHammockNerve C) _⦋m + 1⦌ =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso m 0).hom ≫ SSet.yonedaEquiv.symm z)
    (simplex_naturality C U p hp σ hU Γ t α)

def prism : Δ[1] ⊗ nerve I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kanHammockSourceFunctor C).obj Y))) where
  app _ := ↾fun a => sliceSimplex C U p hp σ hU a.2 (stdSimplex.objEquiv a.1).toOrderHom
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro a
    exact (sliceSimplex_naturality C U p hp σ hU a.2
      (stdSimplex.objEquiv a.1).toOrderHom α.unop).symm

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
