module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RangeCoverGluing

/-!
概要：被覆上の図式を、同じ底の図式を保ったまま像の和上へ接合する。
方針：既存の接合の各被覆上の等式と、全単体の被覆を使って底の等式を反映する。
規約：底を忘れた接合から、元の射影との厳密な可換性も回収する。
使われ方：twisted arrow の相対境界データを right anodyne 延長の入力にする。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 同じ指定底の図式上で、互換な被覆の全族を接合できる。 -/
lemma exists_map_of_compatible_range_cover_over {I : Type v} {Y E B : SSet.{u}}
    (X : I → SSet.{u}) (ι : ∀ i, X i ⟶ Y) (f : ∀ i, X i ⟶ E)
    (p : E ⟶ B) (b : Y ⟶ B) (hb : ∀ i, f i ≫ p = ι i ≫ b)
    (hc : ∀ (i j : I) (d : SimplexCategoryᵒᵖ) (x : (X i).obj d) (y : (X j).obj d),
      (ι i).app d x = (ι j).app d y → (f i).app d x = (f j).app d y) :
    ∃ F : ((⨆ i, Subcomplex.range (ι i) : Y.Subcomplex) : SSet.{u}) ⟶ E,
      (∀ i, Subcomplex.lift (ι i)
        (le_iSup (fun j ↦ Subcomplex.range (ι j)) i) ≫ F = f i) ∧
      F ≫ p = (⨆ i, Subcomplex.range (ι i) : Y.Subcomplex).ι ≫ b := by
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.exists_map_of_compatible_range_cover X ι f hc
  refine ⟨F, hF, ?_⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  have hs := s.property
  change s.val ∈ (⨆ i, Subcomplex.range (ι i)).obj d at hs
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range] at hs
  obtain ⟨i, x, hx⟩ := hs
  let l := Subcomplex.lift (ι i) (le_iSup (fun j ↦ Subcomplex.range (ι j)) i)
  have hl : l.app d x = s := Subtype.ext hx
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app (hF i) d) x
  change F.app d (l.app d x) = (f i).app d x at he
  rw [hl] at he
  change p.app d (F.app d s) = b.app d s.val
  rw [he, ← hx]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (hb i) d) x

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
