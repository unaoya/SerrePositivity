module

public import SerrePositivity.InfinityCategories.Core.JoinPushout

/-!
概要：二項 coproduct の join は共通の右因子に沿う pushout。
方針：slice の普遍性で左右の射を curry して coproduct 上に貼る。
規約：共通の右因子は一度だけ含める。
使われ方：Kerodon Lemma 4.6.4.25 の join の円柱の両端。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの左因子の coproduct との join は、二つの join を右因子で貼った pushout。
方針：slice の curry と coproduct の普遍性を組み合わせる。
規約：単射性や quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.4.25 の共通図式で貼る端点。 -/
lemma join_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (joinInr A K) (joinInr B K)
      (joinMap (coprod.inl : A ⟶ A ⨿ B) (𝟙 K))
      (joinMap (coprod.inr : B ⟶ A ⨿ B) (𝟙 K)) := by
  apply IsPushout.mk'
    (by simp only [joinInr_joinMap, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := joinInr (A ⨿ B) K ≫ φ
    have hψ : joinInr (A ⨿ B) K ≫ ψ = p := by
      have he := congrArg (fun z : join A K ⟶ X ↦ joinInr A K ≫ z) h₁
      simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp] using he.symm
    have hc : sliceOverCurry φ rfl = sliceOverCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [sliceOverCurry_precomp, sliceOverCurry_precomp]
        congr 1
      · rw [sliceOverCurry_precomp, sliceOverCurry_precomp]
        congr 1
    simpa only [sliceOverUncurry_curry] using congrArg sliceOverUncurry hc
  · intro X b c hbc
    let p := joinInr A K ≫ b
    have hc : joinInr B K ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ sliceOver p := coprod.desc (sliceOverCurry b rfl) (sliceOverCurry c hc)
    refine ⟨sliceOverUncurry F, ?_, ?_⟩
    · rw [← sliceOverUncurry_precomp]
      change sliceOverUncurry.{u} ((coprod.inl : A ⟶ A ⨿ B) ≫ F) = b
      rw [coprod.inl_desc, sliceOverUncurry_curry]
    · rw [← sliceOverUncurry_precomp]
      change sliceOverUncurry.{u} ((coprod.inr : B ⟶ A ⨿ B) ≫ F) = c
      rw [coprod.inr_desc, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories
