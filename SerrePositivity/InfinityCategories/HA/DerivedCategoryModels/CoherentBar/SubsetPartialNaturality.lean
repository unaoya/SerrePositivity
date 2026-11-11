module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarSubsetNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DegenerateFaces
/-!
概要：単調写像の部分集合上の単射性だけで bar のラベル自然性を判定する。
方針：昇順列挙の合成の像を計算し、非単射の制限は元の単体の退化性へ送る。
規約：単調写像全体の単射性は要求しない。全単体作用を扱う。
使われ方：正規化 native 余錐の退化写像に対する自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarSubsetLabel_map_of_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (hα : Set.InjOn α (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op s) J r hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s (J.image α) r
        (by rw [Finset.card_image_of_injOn hα]; exact hc) := by
  have hi : Function.Injective (α.comp (J.orderEmbOfFin hc).toOrderHom) := by
    intro a b hab
    apply (J.orderEmbOfFin hc).injective
    exact hα (J.orderEmbOfFin_mem hc a) (J.orderEmbOfFin_mem hc b) hab
  have hs : StrictMono (α.comp (J.orderEmbOfFin hc).toOrderHom) :=
    (α.monotone.comp (J.orderEmbOfFin hc).monotone).strictMono_of_injective hi
  have he : (fun j : Fin (r + 1) => α (J.orderEmbOfFin hc j)) =
      (J.image α).orderEmbOfFin (by rw [Finset.card_image_of_injOn hα]; exact hc) :=
    Finset.orderEmbOfFin_unique _
      (fun j => Finset.mem_image.mpr ⟨_, J.orderEmbOfFin_mem hc j, rfl⟩) hs
  have hm : SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom ≫
      SimplexCategory.mkHom α =
      SimplexCategory.mkHom ((J.image α).orderEmbOfFin
        (by rw [Finset.card_image_of_injOn hα]; exact hc)).toOrderHom := by
    ext j : 3
    exact congrFun he j
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSimplex_map_comp, hm]

lemma dgCoherentBarSubsetLabel_degenerate_of_not_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 1)))
    (hα : ¬Set.InjOn α (J : Set (Fin (m + 1)))) (r : ℕ) (hc : J.card = r + 1) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op s) J r hc).2 ∈
      I.degenerate r := by
  have he : Finset.univ.image (α.comp (J.orderEmbOfFin hc).toOrderHom) = J.image α := by
    change Finset.univ.image ((α : Fin (m + 1) → Fin (n + 1)) ∘ (J.orderEmbOfFin hc)) =
      J.image α
    rw [← Finset.image_image, J.image_orderEmbOfFin_univ hc]
  have hn : ¬Function.Injective (α.comp (J.orderEmbOfFin hc).toOrderHom) := by
    intro hi
    apply hα
    apply Finset.card_image_iff.mp
    rw [← he, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin, hc]
  change I.map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op
    (I.map (SimplexCategory.mkHom α).op s) ∈ I.degenerate r
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSimplex_map_comp]
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBar_map_degenerate_of_not_injective s
    (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom ≫ SimplexCategory.mkHom α) hn

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
