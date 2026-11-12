module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeFixedFront

/-!
# 元の混合 coherent 単体の一端は同じ native Hom 比較

概要：時刻一の全単体を同じ native family の元の coherent Hom 比較単体へ同定する。
方針：通常前面の全恒等と最後 Hom の最大座標公式を使う。
規約：元の全 path・元の Kan Hom・同じ familyMap を保持する。
使われ方：native roof prism の一端の全 pinched 族への同定。
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

lemma simplex_one {n : ℕ} (Γ : Fin (n + 1) ⥤ I) :
    simplex C U p hp σ hU Γ (OrderHom.const _ 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((familyMap C U p hp σ hU).app (Opposite.op ⦋n⦌) Γ) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagram_eq_comparison
    (frontDiagram C U p Γ (OrderHom.const _ 1)) ((kanHammockSourceFunctor C).obj Y)
    (lastHom C U p hp σ hU Γ (OrderHom.const _ 1))
    (lastHom_comp C U p hp σ hU Γ (OrderHom.const _ 1))
    (fun i => frontDiagram_obj_one C U p Γ (OrderHom.const _ 1) i rfl)
    (fun i j hij => frontDiagram_map_one_one C U p Γ (OrderHom.const _ 1) i j hij rfl rfl)
    ((familyMap C U p hp σ hU).app (Opposite.op ⦋n⦌) Γ)
  intro i
  rw [lastHom_one C U p hp σ hU Γ (OrderHom.const _ 1) i rfl]
  have h := SSet.yonedaEquiv_symm_comp (show (nerve I) _⦋n⦌ from Γ)
    (familyMap C U p hp σ hU)
  exact congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ SimplicialCategory.sHom
    ((kanHammockSourceFunctor C).obj X) ((kanHammockSourceFunctor C).obj Y) =>
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ f) h

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
