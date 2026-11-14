module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarSubsetLabels
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarIntervalSimplices

/-!
概要：部分単体のラベルは単射な頂点再添字付けと厳密に両立する。
方針：像集合の昇順列挙を一意性で同定し、元の単体的合成則に戻す。
規約：部分集合と元の単体ラベルの等号を保持する。
使われ方：bar の Bianchi データを任意の部分単体へ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {I : SSet.{u}}

lemma dgCoherentBarSubsetLabel_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (J : Finset (Fin (m + 1))) (r : ℕ) (hc : J.card = r + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel (I.map (SimplexCategory.mkHom α).op σ) J r hc =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (J.image α) r
        (by rw [Finset.card_image_of_injective _ hα]; exact hc) := by
  have hs : StrictMono α := α.monotone.strictMono_of_injective hα
  have he : (fun j : Fin (r + 1) => α (J.orderEmbOfFin hc j)) =
      (J.image α).orderEmbOfFin
        (by rw [Finset.card_image_of_injective _ hα]; exact hc) :=
    Finset.orderEmbOfFin_unique _
      (fun j => Finset.mem_image.mpr ⟨_, J.orderEmbOfFin_mem hc j, rfl⟩)
      (hs.comp (J.orderEmbOfFin hc).strictMono)
  have hm : SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom ≫
      SimplexCategory.mkHom α =
      SimplexCategory.mkHom ((J.image α).orderEmbOfFin
        (by rw [Finset.card_image_of_injective _ hα]; exact hc)).toOrderHom := by
    ext j : 3
    exact congrFun he j
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel
  congr 1
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSimplex_map_comp, hm]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
