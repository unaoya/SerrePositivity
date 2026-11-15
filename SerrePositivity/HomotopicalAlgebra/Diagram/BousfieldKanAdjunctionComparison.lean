module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanAdjunctionUnit

/-!
概要：右随伴による指定BK frame実現の添字変更は弱同値。
方針：指定単位による逆の候補を、余単位の円柱と三角恒等式で照合する。
使われ方：HTT 4.2.4.4、RR02(a)の要素圏からOverへの実際の比較。
規約：任意の置換した比較でなく、元の指定添字変更射の弱同値性を示す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C] [ModelCategory C]
  {S : K ⥤ L} {P : L ⥤ K} (adj : S ⊣ P) (A : K ⥤ SimplexCategory ⥤ C)
  (hA : ∀ k, reedyLeft simplex (cofibrations C) (initial.to (A.obj k)))
  (hconst : ∀ k, ∀ {n m : SimplexCategory} (f : n ⟶ m),
    weakEquivalences C ((A.obj k).map f))

include adj hA hconst in
lemma reindex_comp_adjointInverse_localization :
    (weakEquivalences C).Q.map
      (bousfieldKanReindexMap P A ≫ adjointReindexInverse adj A) = 𝟙 _ := by
  let R := (weakEquivalences C).Q
  have hc := bousfieldKanReindexMap_localization_naturality adj.counit (P ⋙ A)
    (fun l => hA (P.obj (S.obj (P.obj l))))
    (fun l _ _ f => hconst (P.obj (S.obj (P.obj l))) f)
  rw [bousfieldKanReindexMap_id, Category.comp_id] at hc
  have hn := bousfieldKanReindexMap_frame_naturality P (Functor.whiskerRight adj.unit A)
  simp only [CategoryTheory.Functor.id_comp, CategoryTheory.Functor.assoc] at hn
  unfold adjointReindexInverse
  rw [← Category.assoc, hn, Category.assoc, bousfieldKanReindexMap_comp,
    CategoryTheory.Functor.map_comp, hc, ← CategoryTheory.Functor.map_comp,
    ← NatTrans.comp_app, ← map_comp, adjointReindex_coefficient_triangle, map_id]
  simp

include adj hA hconst in
/-- 指定右随伴のBK添字変更射は、元のモデル圏で弱同値。 -/
lemma bousfieldKanReindexMap_weakEquivalence_of_adjunction :
    weakEquivalences C (bousfieldKanReindexMap P A) := by
  let R := (weakEquivalences C).Q
  let e : R.obj ((functor L (P ⋙ A)).obj (bousfieldKanWeight Lᵒᵖ)) ≅
      R.obj ((functor K A).obj (bousfieldKanWeight Kᵒᵖ)) :=
    { hom := R.map (bousfieldKanReindexMap P A)
      inv := R.map (adjointReindexInverse adj A)
      hom_inv_id := by
        rw [← R.map_comp]
        exact reindex_comp_adjointInverse_localization adj A hA hconst
      inv_hom_id := by
        rw [← R.map_comp]
        exact adjointReindexInverse_comp_localization adj A hA hconst }
  exact (Quillen.weakEquivalences_iff_isIso_map R _).mpr e.isIso_hom

end SerrePositivity.DiagramModel.FrameWeightRealization
