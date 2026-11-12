module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.ContinuousKanRelativeReflection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CylinderBoundaryMono

/-!
概要：Kan 置換内の指定 path を、元の両端を固定した比較とともに元の Kan 対象へ戻す。
方針：path の二端点を指定境界にして相対反映を適用する。
規約：元の指定 path への比較円柱は両端上で全時刻定値。
使われ方：共通値へ輸送した path の元の値での検出。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定 Kan path は、元の値の path の像と端点固定でホモトピック。
方針：二端点の直和を境界として、元の指定円柱を相対的に反映する。
規約：比較の始端は返した path の全円柱の像。使われ方：標的 path の同時有限検出。 -/
lemma continuousKanReplacement_path_reflection {K X : SSet.{u}} [KanComplex X]
    (f g : K ⟶ X) (H : SSet.Homotopy (f ≫ continuousKanReplacementUnit.app X)
      (g ≫ continuousKanReplacementUnit.app X)) :
    ∃ L : SSet.Homotopy f g,
      ∃ G : SSet.Homotopy (L.h ≫ continuousKanReplacementUnit.app X) H.h,
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc f g ≫
            continuousKanReplacementUnit.app X := by
  have hh : cylinderBoundaryInclusion K ≫ H.h =
      coprod.desc f g ≫ continuousKanReplacementUnit.app X := by
    apply coprod.hom_ext
    · simp only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inl_desc, H.h₀]
    · simp only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inr_desc, H.h₁]
  obtain ⟨v, hv, G, hG⟩ := continuousKanReplacement_relative_reflection
    (cylinderBoundaryInclusion K) (coprod.desc f g) H.h hh
  let L : SSet.Homotopy f g :=
    { h := v
      h₀ := by
        change SSet.ι₀ ≫ v = f
        have h := congrArg (fun r ↦ (coprod.inl : K ⟶ K ⨿ K) ≫ r) hv
        simpa only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inl_desc] using h
      h₁ := by
        change SSet.ι₁ ≫ v = g
        have h := congrArg (fun r ↦ (coprod.inr : K ⟶ K ⨿ K) ≫ r) hv
        simpa only [cylinderBoundaryInclusion, ← Category.assoc, coprod.inr_desc] using h
      rel := by
        apply SSet.hom_ext
        intro n
        apply ConcreteCategory.hom_ext
        intro x
        exact False.elim x.1.property }
  exact ⟨L, G, hG⟩

end SerrePositivity.InfinityCategories.F2
