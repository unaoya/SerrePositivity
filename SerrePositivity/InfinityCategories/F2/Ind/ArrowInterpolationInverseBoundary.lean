module

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeSurjective

/-!
概要：全円柱同型の逆は、元の円柱・始点余錐・補間領域を厳密に回収する。
方針：構成済みの順比較との合成で同じ全境界の等式に戻す。
規約：元の包含写像を変えない。使われ方：全円柱延長から元の全変換への帰還。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 逆比較は、元の全補間領域を同じ余錐の左因子として回収。 -/
lemma arrowInterpolationCoconeIso_inv_inclusion (A : SSet.{u}) :
    arrowInterpolationCornerInclusion A ≫ (arrowInterpolationCoconeIso A).inv =
      joinInl (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) := by
  apply (cancel_mono (arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationCocone_inl A).symm

/-- 逆比較は、元の全円柱側を同じ貼り合わせ側の左包含に戻す。 -/
lemma arrowInterpolationCoconeIso_inv_old (A : SSet.{u}) :
    (joinInl A (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ (arrowInterpolationCoconeIso A).inv =
      pushout.inl SSet.ι₀ (joinInl A Δ[0]) ≫
        joinInl (arrowInterpolationCorner A) Δ[0] := by
  apply (cancel_mono (arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationCocone_old A).symm

/-- 逆比較は、元の全始点余錐側を同じ貼り合わせ側の右包含に戻す。 -/
lemma arrowInterpolationCoconeIso_inv_source (A : SSet.{u}) :
    (SSet.ι₀ : join A (Δ[0] : SSet.{u}) ⟶ join A Δ[0] ⊗ Δ[1]) ≫
      (arrowInterpolationCoconeIso A).inv =
        pushout.inr SSet.ι₀ (joinInl A Δ[0]) ≫ joinInl (arrowInterpolationCorner A) Δ[0] := by
  apply (cancel_mono (arrowInterpolationCoconeIso A).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (arrowInterpolationCocone_source A).symm

end SerrePositivity.InfinityCategories.F2.Ind
