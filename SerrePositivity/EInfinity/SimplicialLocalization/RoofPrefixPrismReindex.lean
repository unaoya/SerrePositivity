module

public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixPrismLast

/-!
# 元の混合前面と最後 Hom の全添字変換

概要：元の通常前面と時刻で切り替えた最後 Hom が全ての面・退化と整合する。
方針：同じ最大座標の自然性・元の prefix path の自然性・端点の正規化を使う。
規約：元の図式・時間・全 path・同じ Kan Hom を保持する。
使われ方：mixed coherent 単体を全 slice prism に束ねる。
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

lemma frontDiagram_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) :
    frontDiagram C U p (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) =
      α.toOrderHom.monotone.functor ⋙ frontDiagram C U p Γ t := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intros
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma lastHom_reindex {m n : ℕ} (Γ : Fin (n + 1) ⥤ I)
    (t : Fin (n + 1) →o Fin 2) (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i) ≫ lastHom C U p hp σ hU Γ t (α.toOrderHom i) =
      lastHom C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ) (t.comp α.toOrderHom) i := by
  by_cases hi : t (α.toOrderHom i) = 0
  · apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (frontDiagram_obj_zero C U p (α.toOrderHom.monotone.functor ⋙ Γ)
        (t.comp α.toOrderHom) i hi) (rfl : (kanHammockSourceFunctor C).obj Y = _)))).1
    simp only [Category.assoc]
    rw [lastHom_zero C U p hp σ hU Γ t (α.toOrderHom i) hi,
      lastHom_zero C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ)
        (t.comp α.toOrderHom) i hi]
    exact pathMap_reindex C U p hp σ hU Γ t α i
  · have hi1 : t (α.toOrderHom i) = 1 := by omega
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (frontDiagram_obj_one C U p (α.toOrderHom.monotone.functor ⋙ Γ)
        (t.comp α.toOrderHom) i hi1) (rfl : (kanHammockSourceFunctor C).obj Y = _)))).1
    simp only [Category.assoc]
    rw [lastHom_one C U p hp σ hU Γ t (α.toOrderHom i) hi1,
      lastHom_one C U p hp σ hU (α.toOrderHom.monotone.functor ⋙ Γ)
        (t.comp α.toOrderHom) i hi1]
    have hΓ : SSet.stdSimplex.map α ≫ SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ) =
        SSet.yonedaEquiv.symm (show (nerve I) _⦋m⦌ from
          α.toOrderHom.monotone.functor ⋙ Γ) := by
      rw [SSet.yonedaEquiv_symm_naturality_left]
      rfl
    rw [← Category.assoc (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap (α.toOrderHom i)), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap_naturality]
    simp only [Category.assoc]
    rw [← Category.assoc (SSet.stdSimplex.map α)
      (SSet.yonedaEquiv.symm (show (nerve I) _⦋n⦌ from Γ)), hΓ]

end SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefix
