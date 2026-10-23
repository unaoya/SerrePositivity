module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCornerMap
public import SerrePositivity.InfinityCategories.F2.Ind.ConeFoldNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeSurjective

/-!
概要：実補間領域の余錐と全円柱の同型は、元の形状制限に自然。
方針：二座標への射影を、元の包含の自然性と二重点の折り畳みで計算する。
規約：同じ全写像を保持。使われ方：補間族の制限と再構成円柱の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A B : SSet.{u}} (f : A ⟶ B)

/-- 補間領域の余錐から元の全円柱への同じ比較は、全形状の制限と可換。 -/
lemma arrowInterpolationCocone_naturality :
    joinMap (arrowInterpolationCornerMap f) (𝟙 Δ[0]) ≫ arrowInterpolationCocone B =
      arrowInterpolationCocone A ≫ (joinMap f (𝟙 Δ[0]) ▷ (Δ[1] : SSet.{u})) := by
  have hx : arrowInterpolationCornerMap f ≫ arrowInterpolationCornerInclusion B ≫ fst _ _ =
      (arrowInterpolationCornerInclusion A ≫ fst _ _) ≫ joinMap f (𝟙 Δ[0]) := by
    rw [← Category.assoc, arrowInterpolationCornerInclusion_naturality, Category.assoc,
      whiskerRight_fst, ← Category.assoc]
  have hy : arrowInterpolationCornerMap f ≫ arrowInterpolationCornerInclusion B ≫ snd _ _ =
      arrowInterpolationCornerInclusion A ≫ snd _ _ := by
    rw [← Category.assoc, arrowInterpolationCornerInclusion_naturality, Category.assoc,
      whiskerRight_snd]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, arrowInterpolationCocone, lift_fst, lift_fst_assoc, whiskerRight_fst]
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hx]
    rw [← arrowInterpolationConeFold_naturality, ← Category.assoc, ← joinMap_comp,
      Category.id_comp]
  · simp only [Category.assoc, arrowInterpolationCocone, lift_snd, whiskerRight_snd]
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hy]

/-- 全円柱を実余錐へ戻す同じ逆同型も、全形状の制限と可換。 -/
lemma arrowInterpolationCoconeIso_inv_naturality :
    (joinMap f (𝟙 Δ[0]) ▷ (Δ[1] : SSet.{u})) ≫ (arrowInterpolationCoconeIso B).inv =
      (arrowInterpolationCoconeIso A).inv ≫
        joinMap (arrowInterpolationCornerMap f) (𝟙 Δ[0]) := by
  apply (cancel_mono (arrowInterpolationCoconeIso B).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = (arrowInterpolationCoconeIso A).inv ≫
    joinMap (arrowInterpolationCornerMap f) (𝟙 Δ[0]) ≫ arrowInterpolationCocone B
  rw [arrowInterpolationCocone_naturality, ← Category.assoc]
  change _ = (arrowInterpolationCoconeIso A).inv ≫
    (arrowInterpolationCoconeIso A).hom ≫ (joinMap f (𝟙 Δ[0]) ▷ Δ[1])
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
