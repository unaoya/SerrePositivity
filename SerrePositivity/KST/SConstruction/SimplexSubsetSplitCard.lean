module
public import SerrePositivity.KST.SConstruction.SimplexSubsetSplitRange

/-! # 元の左右部分集合の濃度
概要：元の切断局所番号から、左右フィルターの頂点数を回収する。
方針：元の包含の像を有限始端・終端区間と同定し、単射性から濃度を計算する。
規約：共有頂点を両側に含める。使われ方：二 bead の元の長さと左右ブロックの同定。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の左部分集合の濃度は、元の切断局所番号に一を加えた値。 -/
lemma simplexSubsetSplitLeft_card {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hL : 2 ≤ (I.filter (· ≤ j)).card) :
    (I.filter (· ≤ j)).card = (simplexSubsetVertexIndex I hI j hj).val + 1 := by
  have he : Finset.image
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (· ≤ j)) I hL hI (Finset.filter_subset _ _))
      Finset.univ = Finset.Iic (simplexSubsetVertexIndex I hI j hj) := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.coe_Iic] using
      simplexSubsetSplitLeft_range I hI j hj hL
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_injective
    (I.filter (· ≤ j)) I hL hI (Finset.filter_subset _ _)),
    Finset.card_univ, Fintype.card_fin, Fin.card_Iic] at hc
  omega

/-- 元の右部分集合の濃度は、元の全頂点数から切断局所番号を引いた値。 -/
lemma simplexSubsetSplitRight_card {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (j : Fin (n + 1)) (hj : j ∈ I) (hR : 2 ≤ (I.filter (j ≤ ·)).card) :
    (I.filter (j ≤ ·)).card = I.card - (simplexSubsetVertexIndex I hI j hj).val := by
  have he : Finset.image
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder (I.filter (j ≤ ·)) I hR hI (Finset.filter_subset _ _))
      Finset.univ = Finset.Ici (simplexSubsetVertexIndex I hI j hj) := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Finset.coe_Ici] using
      simplexSubsetSplitRight_range I hI j hj hR
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetInclusionOrder_injective
    (I.filter (j ≤ ·)) I hR hI (Finset.filter_subset _ _)),
    Finset.card_univ, Fintype.card_fin, Fin.card_Ici] at hc
  omega

end SerrePositivity.KST.SConstruction
