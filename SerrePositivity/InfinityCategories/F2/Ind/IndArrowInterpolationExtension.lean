module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationCocone
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationExtension

/-!
概要：元の円柱族と始点余錐を同時に保つ、実 Ind comma 上の全円柱延長。
方針：κ-small な補間領域で実余錐を取り、構成した全形状同型の逆で戻す。
規約：元の両全図式を厳密に保持。使われ方：射の filtered 表示の終点追加。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 実 scalar comma 内で、元の円柱と始点余錐を同時に延長できる。 -/
lemma exists_indComma_arrowInterpolation_extension (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {C A : SSet.{u}} [Quasicategory C] (x : (IndInfinity κ C) _⦋0⦌)
    (hA : IsKappaSmall κ A)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (A ⊗ Δ[1]) ⟶
      leftKanShape (indYoneda κ C) x)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
      leftKanShape (indYoneda κ C) x)
    (h : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ F =
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G) :
    ∃ E : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶
        leftKanShape (indYoneda κ C) x,
      (SSet.uliftFunctor.{u + 1, u}).map
        (joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫ E = F ∧
      (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ E = G := by
  obtain ⟨H, ⟨c⟩, hF, hG⟩ := exists_indComma_arrowInterpolation_cocone κ x hA F G h
  let E := arrowInterpolationExtend.{u, u + 1} c
  have he : (SSet.uliftFunctor.{u + 1, u}).map (arrowInterpolationCornerInclusion A) ≫ E = H :=
    arrowInterpolationExtend_inclusion c
  refine ⟨E, ?_, ?_⟩
  · rw [← arrowInterpolationCornerInclusion_old, Functor.map_comp, Category.assoc, he, hF]
  · rw [← arrowInterpolationCornerInclusion_source, Functor.map_comp, Category.assoc, he, hG]

end SerrePositivity.InfinityCategories.F2.Ind
