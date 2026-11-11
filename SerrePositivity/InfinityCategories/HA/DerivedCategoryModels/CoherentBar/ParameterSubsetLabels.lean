module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.SubsetPartialNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarSubsetCuts
/-!
概要：パラメーター部分単体の標準面を、元の集合の一点削除ラベルへ戻す。
方針：単射な昇順列挙と既存の部分単体ラベルの自然性を使う。
規約：任意の単体集合と宇宙で成立する純粋な添字の等式。
使われ方：回収した Hom の境界式を pinched Hom の全部分集合方程式へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial

private lemma subsetLabel_congr {I : SSet.{u}} {n : ℕ} (s : I _⦋n⦌)
    {J K : Finset (Fin (n + 1))} (h : J = K) (r : ℕ)
    (hJ : J.card = r + 1) (hK : K.card = r + 1) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s J r hJ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s K r hK := by
  cases h
  rfl

lemma dgCoherentBarSubsetLabel_erase_face {I : SSet.{u}} {m n : ℕ}
    (s : I _⦋n⦌) (J : Finset (Fin (n + 1))) (hc : J.card = m + 2) (i : Fin (m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s (J.erase (J.orderEmbOfFin hc i)) m
      (by rw [Finset.card_erase_of_mem (J.orderEmbOfFin_mem hc i), hc]; omega) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFace (I.map (SimplexCategory.mkHom (J.orderEmbOfFin hc).toOrderHom).op s) i := by
  let α := (J.orderEmbOfFin hc).toOrderHom
  have hα : Function.Injective α := (J.orderEmbOfFin hc).injective
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarSubsetLabel_map_of_injOn s α
    (Finset.univ.erase i) hα.injOn m (by simp)
  have him : (Finset.univ.erase i).image α = J.erase (J.orderEmbOfFin hc i) := by
    rw [Finset.image_erase hα]
    exact congrArg (fun K => K.erase (α i)) (J.image_orderEmbOfFin_univ hc)
  have h2 := subsetLabel_congr s him m
    (by rw [Finset.card_image_of_injective _ hα]; simp)
    (by rw [Finset.card_erase_of_mem (J.orderEmbOfFin_mem hc i), hc]; omega)
  exact (h.trans h2).symm.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_face _ i)

lemma dgCoherentBarFin_strictRight_card (n : ℕ) (i : Fin (n + 1)) :
    ((Finset.univ : Finset (Fin (n + 1))).filter (i < ·)).card = n - i.val := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 1)))) (fun x => x ≤ i)
  simp only [not_le] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefix_card n i, Finset.card_univ, Fintype.card_fin] at h
  omega

lemma dgCoherentBarSubset_strictRight_card {m n : ℕ}
    (J : Finset (Fin (n + 1))) (hc : J.card = m + 1) (i : Fin (m + 1)) :
    (J.filter (J.orderEmbOfFin hc i < ·)).card = m - i.val := by
  let α := (J.orderEmbOfFin hc).toOrderHom
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_sign_card (I := (Finset.univ : Finset (Fin (m + 1))))
    α.monotone (J.orderEmbOfFin hc).injective.injOn (Finset.mem_univ i)
  have him : Finset.univ.image α = J := J.image_orderEmbOfFin_univ hc
  rw [him] at h
  exact h.trans (dgCoherentBarFin_strictRight_card m i)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
