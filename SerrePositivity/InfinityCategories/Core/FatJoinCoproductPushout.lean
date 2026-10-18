module

public import SerrePositivity.InfinityCategories.Core.LaxSliceNaturality

/-!
概要：二項 coproduct の fatJoin は共通の右因子に沿う pushout。
方針：slice の普遍性で左右の射を curry して coproduct 上に貼る。
規約：共通の右因子は一度だけ含める。
使われ方：Kerodon Lemma 4.6.4.25 の fatJoin の円柱の両端。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの左因子の coproduct との fatJoin は、二つの fatJoin を右因子で貼った pushout。
方針：slice の curry と coproduct の普遍性を組み合わせる。
規約：単射性や quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.4.25 の共通図式で貼る端点。 -/
lemma fatJoin_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (fatJoinInr A K) (fatJoinInr B K)
      (fatJoinMap (coprod.inl : A ⟶ A ⨿ B) (𝟙 K))
      (fatJoinMap (coprod.inr : B ⟶ A ⨿ B) (𝟙 K)) := by
  apply IsPushout.mk'
    (by simp only [fatJoinInr_map, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := fatJoinInr (A ⨿ B) K ≫ φ
    have hψ : fatJoinInr (A ⨿ B) K ≫ ψ = p := by
      have he := congrArg (fun z : fatJoin A K ⟶ X ↦ fatJoinInr A K ≫ z) h₁
      simpa only [← Category.assoc, fatJoinInr_map, Category.id_comp] using he.symm
    have hc : laxSliceCurry φ rfl = laxSliceCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [← laxSliceCurry_precomp, ← laxSliceCurry_precomp]
        congr 1
      · rw [← laxSliceCurry_precomp, ← laxSliceCurry_precomp]
        congr 1
    simpa only [laxSliceUncurry_curry] using congrArg laxSliceUncurry hc
  · intro X b c hbc
    let p := fatJoinInr A K ≫ b
    have hc : fatJoinInr B K ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ laxSlice p := coprod.desc (laxSliceCurry b rfl) (laxSliceCurry c hc)
    refine ⟨laxSliceUncurry F, ?_, ?_⟩
    · rw [← laxSliceUncurry_precomp]
      change laxSliceUncurry.{u} ((coprod.inl : A ⟶ A ⨿ B) ≫ F) = b
      rw [coprod.inl_desc, laxSliceUncurry_curry]
    · rw [← laxSliceUncurry_precomp]
      change laxSliceUncurry.{u} ((coprod.inr : B ⟶ A ⨿ B) ≫ F) = c
      rw [coprod.inr_desc, laxSliceUncurry_curry]

end SerrePositivity.InfinityCategories
