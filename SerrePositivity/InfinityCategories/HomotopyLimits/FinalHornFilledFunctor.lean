module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornFillHom
public import SerrePositivity.InfinityCategories.Coherent.UnitComposition

/-!
# 最終外側ホーンの豊穣単体への復元

概要：最終外側ホーンの二つの未知 Hom を、元の豊穣単体と相対充填へ組み立てる。
方針：全三対象の合成、全既知面への制限、薄い底の一意性を順に照合する。
規約：元の cf 置換と底射影を使い、内ホーンの欠損頂点条件を仮定しない。
使われ方：HTT 5.2.4.6 の元の右 Quillen 候補辺の Cartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory HomotopicalAlgebra MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve C)
  (g : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (Fin.last (n + 2)))) ⟶
      SimplicialCategory.sHom (hornObj σ 0) (hornObj σ (Fin.last (n + 2))))
  (f : nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 3)))
    (ULift.up (finalHornPenultimate n))) ⟶
      SimplicialCategory.sHom (hornObj σ 0) (hornObj σ (finalHornPenultimate n)))

/-- 前半の未知 Hom は、全境界上の合成面条件から全内部切断点で合成を保存する。 -/
lemma finalHornFillHom_comp_front
    (hf : ∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom σ j)
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n) :
    pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (finalHornPenultimate n)) ≫
        finalHornFillHom σ g f 0 (finalHornPenultimate n) =
      (finalHornFillHom σ g f 0 b ⊗ₘ finalHornFillHom σ g f b (finalHornPenultimate n)) ≫
        SimplicialCategory.sHomComp (hornObj σ 0) (hornObj σ b)
          (hornObj σ (finalHornPenultimate n)) := by
  rw [finalHornFillHom_front,
    finalHornFillHom_known σ g f 0 b (Fin.zero_le b) (Or.inr hbp),
    finalHornFillHom_known σ g f b (finalHornPenultimate n) (le_of_lt hbp)
      (Or.inl (ne_of_gt hb0))]
  have hb := hf (.inr ⟨ULift.up.{u} b, hb0, hbp⟩)
  change (pathThrough (ULift.up b)).ι ≫ f = finalHornFrontCompositionHom σ b hb0 hbp at hb
  rw [← pathThroughIso_hom_ι, Category.assoc, hb]
  exact finalHornCompositionHom_on_product σ 0 b (finalHornPenultimate n)
    (Fin.zero_le b) (le_of_lt hbp) (Or.inr hbp) (Or.inl (ne_of_gt hb0))

/-- 全区間の未知 Hom は、既知合成面と penultimate 合成面の条件から合成を保存する。 -/
lemma finalHornFillHom_comp_full
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
      (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (hornObj σ 0) (finalHornLastArrow σ) =
      finalHornAppend n ≫ g)
    (b : Fin (n + 3)) (hb0 : 0 < b) (hbn : b < Fin.last (n + 2)) :
    pathCompMap (ULift.up.{u} (0 : Fin (n + 3))) (ULift.up b)
      (ULift.up (Fin.last (n + 2))) ≫ finalHornFillHom σ g f 0 (Fin.last (n + 2)) =
      (finalHornFillHom σ g f 0 b ⊗ₘ finalHornFillHom σ g f b (Fin.last (n + 2))) ≫
        SimplicialCategory.sHomComp (hornObj σ 0) (hornObj σ b) (hornObj σ (Fin.last (n + 2))) := by
  rw [finalHornFillHom_full,
    finalHornFillHom_known σ g f b (Fin.last (n + 2)) (Fin.le_last b)
      (Or.inl (ne_of_gt hb0))]
  by_cases hbp : b = finalHornPenultimate n
  · subst b
    rw [finalHornFillHom_front, ← pathThroughIso_hom_ι, Category.assoc,
      finalHornFrontHom_postcomposition_composition σ g f hfg]
    simp only [Iso.hom_inv_id_assoc]
  · have hbp' := lt_finalHornPenultimate_of_lt_last_ne b hbn hbp
    rw [finalHornFillHom_known σ g f 0 b (Fin.zero_le b) (Or.inr hbp'),
      ← pathThroughIso_hom_ι, Category.assoc, hg b hb0 hbp']
    exact finalHornCompositionHom_on_product σ 0 b (Fin.last (n + 2))
      (Fin.zero_le b) (Fin.le_last b) (Or.inr hbp') (Or.inl (ne_of_gt hb0))

/-- 充填用 Hom は、順序外と単位を含む全三対象の元の豊穣合成を保存する。 -/
lemma finalHornFillHom_comp
    (hf : ∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
      (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (hornObj σ 0) (finalHornLastArrow σ) =
      finalHornAppend n ≫ g) (a b c : Fin (n + 3)) :
    pathCompMap (ULift.up.{u} a) (ULift.up b) (ULift.up c) ≫ finalHornFillHom σ g f a c =
      (finalHornFillHom σ g f a b ⊗ₘ finalHornFillHom σ g f b c) ≫
        SimplicialCategory.sHomComp (hornObj σ a) (hornObj σ b) (hornObj σ c) := by
  by_cases hab : a ≤ b
  swap
  · exact pathProduct_empty_hom_ext (ULift.up.{u} a) (ULift.up b) (ULift.up c) (Or.inl hab) _ _
  by_cases hbc : b ≤ c
  swap
  · exact pathProduct_empty_hom_ext (ULift.up.{u} a) (ULift.up b) (ULift.up c) (Or.inr hbc) _ _
  by_cases heab : a = b
  · subst b
    exact pathHom_comp_left_unit _ _ _ _ _ _ (finalHornFillHom_id σ g f a)
  by_cases hebc : b = c
  · subst c
    exact pathHom_comp_right_unit _ _ _ _ _ _ (finalHornFillHom_id σ g f b)
  by_cases hpac : FinalHornKnownInterval a c
  · have hpab : FinalHornKnownInterval a b := by
      rcases hpac with ha | hc
      · exact Or.inl ha
      · exact Or.inr (lt_of_le_of_lt hbc hc)
    have hpbc : FinalHornKnownInterval b c := by
      rcases hpac with ha | hc
      · left
        intro hb
        exact ha (le_antisymm (hb ▸ hab) (Fin.zero_le a))
      · exact Or.inr hc
    rw [finalHornFillHom_known σ g f a c (hab.trans hbc) hpac,
      finalHornFillHom_known σ g f a b hab hpab,
      finalHornFillHom_known σ g f b c hbc hpbc]
    exact finalHornKnownIntervalHom_comp σ a b c hab hbc hpab hpbc hpac
  obtain ⟨rfl, hc | hc⟩ := finalHornUnknownInterval_endpoints a c hpac
  · subst c
    exact finalHornFillHom_comp_front σ g f hf b
      (lt_of_le_of_ne hab heab) (lt_of_le_of_ne hbc hebc)
  · subst c
    exact finalHornFillHom_comp_full σ g f hg hfg b
      (lt_of_le_of_ne hab heab) (lt_of_le_of_ne hbc hebc)

/-- 既知区間と二つの未知 Hom から、元の全頂点上の native な豊穣関手を復元する。 -/
def finalHornFilledFunctor
    (hf : ∀ j, (pathCubeBoundaryFace j).ι ≫ f = finalHornFrontBoundaryFaceHom σ j)
    (hg : ∀ (b : Fin (n + 3)) (hb0 : 0 < b) (hbp : b < finalHornPenultimate n),
      (pathThrough (ULift.up b)).ι ≫ g = finalHornUpperCompositionHom σ b hb0 hbp)
    (hfg : f ≫ eHomWhiskerLeft SSet (hornObj σ 0) (finalHornLastArrow σ) =
      finalHornAppend n ≫ g) :
    EnrichedFunctor SSet (SimplicialThickening (ULift.{u} (Fin (n + 3)))) C where
  obj X := hornObj σ X.as.down
  map X Y := finalHornFillHom σ g f X.as.down Y.as.down
  map_id X := finalHornFillHom_id σ g f X.as.down
  map_comp X Y Z := finalHornFillHom_comp σ g f hf hg hfg X.as.down Y.as.down Z.as.down

end
end SerrePositivity.InfinityCategories.HomotopyLimits
