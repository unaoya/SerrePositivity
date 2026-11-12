module

public import Mathlib.CategoryTheory.Limits.Shapes.End
public import Mathlib.CategoryTheory.Comma.CardinalArrow

/-!
概要：小さい圏の end を計算する multicospan の全射の総数を評価する。
方針：対象は元の対象と射、射は恒等射と二つの標準射の直和で被覆する。
規約：対象だけでなく全 Arrow の個数を同じ濃度で抑える。
使われ方：μ-filtered 余極限と weighted sections の end の交換。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の圏の射が μ 個未満なら、end の multicospan の対象も μ 個未満。 -/
lemma hasCardinalLT_endIndex {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (I : Type u) [SmallCategory I] (hI : HasCardinalLT (Arrow I) μ) :
    HasCardinalLT (WalkingMulticospan (multicospanShapeEnd I)) μ := by
  have hObj := hasCardinalLT_of_hasCardinalLT_arrow hI
  have hs : HasCardinalLT (I ⊕ Arrow I) μ := (hasCardinalLT_sum_iff _ _ _ hμ).mpr ⟨hObj, hI⟩
  exact hs.of_surjective (show I ⊕ Arrow I → WalkingMulticospan (multicospanShapeEnd I) from
    Sum.elim (WalkingMulticospan.left (J := multicospanShapeEnd I))
      (WalkingMulticospan.right (J := multicospanShapeEnd I)))
    (by
      rintro (i | f)
      · exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr f, rfl⟩)

/-- 同じ multicospan の全射も、恒等射と二種の標準射で μ 個未満に抑えられる。 -/
lemma hasCardinalLT_endIndex_arrow {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    (I : Type u) [SmallCategory I] (hI : HasCardinalLT (Arrow I) μ) :
    HasCardinalLT (Arrow (WalkingMulticospan (multicospanShapeEnd I))) μ := by
  have hArrows : HasCardinalLT (Arrow I ⊕ Arrow I) μ :=
    (hasCardinalLT_sum_iff _ _ _ hμ).mpr ⟨hI, hI⟩
  have hs : HasCardinalLT
      (WalkingMulticospan (multicospanShapeEnd I) ⊕ Arrow I ⊕ Arrow I) μ :=
    (hasCardinalLT_sum_iff _ _ _ hμ).mpr ⟨hasCardinalLT_endIndex hμ I hI, hArrows⟩
  apply hs.of_surjective (show
    (WalkingMulticospan (multicospanShapeEnd I) ⊕ Arrow I ⊕ Arrow I) →
      Arrow (WalkingMulticospan (multicospanShapeEnd I)) from Sum.elim (fun X ↦ Arrow.mk (𝟙 X))
    (Sum.elim (fun f ↦ Arrow.mk (WalkingMulticospan.Hom.fst (J := multicospanShapeEnd I) f))
      (fun f ↦ Arrow.mk (WalkingMulticospan.Hom.snd (J := multicospanShapeEnd I) f))))
  rintro ⟨_, _, f⟩
  cases f with
  | id => exact ⟨Sum.inl _, rfl⟩
  | fst f => exact ⟨Sum.inr (Sum.inl f), rfl⟩
  | snd f => exact ⟨Sum.inr (Sum.inr f), rfl⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
