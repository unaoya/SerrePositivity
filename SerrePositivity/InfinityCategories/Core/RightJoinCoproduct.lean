module
public import SerrePositivity.InfinityCategories.Core.Coslice
public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.SliceMap
public import SerrePositivity.InfinityCategories.Core.LaxCoslice
public import SerrePositivity.InfinityCategories.Core.LaxCosliceNaturality
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUncurry
public import SerrePositivity.InfinityCategories.Core.LaxCosliceUniversal

/-! # 右因子の coproduct と join

概要：共通の左因子を持つ二つの余錐を、右因子の coproduct で貼り合わせる。
方針：通常の coslice と太い coslice の普遍性を使う。
規約：quasicategory 性を必要としない。使われ方：余錐の族の同型判定。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：右因子の coproduct との join は共通の左因子で貼った pushout。
方針：coslice の普遍性と coproduct の普遍性を組み合わせる。
規約：左図式を固定する。使われ方：余錐の可逆円柱の二端。 -/
lemma join_right_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (joinInl K A) (joinInl K B)
      (joinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ B))
      (joinMap (𝟙 K) (coprod.inr : B ⟶ A ⨿ B)) := by
  apply IsPushout.mk'
    (by simp only [joinInl_joinMap, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := joinInl K (A ⨿ B) ≫ φ
    have hψ : joinInl K (A ⨿ B) ≫ ψ = p := by
      have he := congrArg (fun z : join K A ⟶ X ↦ joinInl K A ≫ z) h₁
      simpa only [← Category.assoc, joinInl_joinMap, Category.id_comp] using he.symm
    have hc : sliceUnderCurry φ rfl = sliceUnderCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [sliceUnderCurry_precomp, sliceUnderCurry_precomp]
        congr 1
      · rw [sliceUnderCurry_precomp, sliceUnderCurry_precomp]
        congr 1
    simpa only [sliceUnderUncurry_curry] using congrArg sliceUnderUncurry hc
  · intro X b c hbc
    let p := joinInl K A ≫ b
    have hc : joinInl K B ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ sliceUnder p := coprod.desc (sliceUnderCurry b rfl) (sliceUnderCurry c hc)
    refine ⟨sliceUnderUncurry F, ?_, ?_⟩
    · rw [← sliceUnderUncurry_precomp]
      rw [coprod.inl_desc, sliceUnderUncurry_curry]
    · rw [← sliceUnderUncurry_precomp]
      rw [coprod.inr_desc, sliceUnderUncurry_curry]


/-- 概要：右因子の coproduct との fatJoin は共通の左因子で貼った pushout。
方針：coslice の普遍性と coproduct の普遍性を組み合わせる。
規約：左図式を固定する。使われ方：余錐の可逆円柱の二端。 -/
lemma fatJoin_right_coproduct_isPushout (A B K : SSet.{u}) :
    IsPushout (fatJoinInl K A) (fatJoinInl K B)
      (fatJoinMap (𝟙 K) (coprod.inl : A ⟶ A ⨿ B))
      (fatJoinMap (𝟙 K) (coprod.inr : B ⟶ A ⨿ B)) := by
  apply IsPushout.mk'
    (by simp only [fatJoinInl_map, Category.id_comp])
  · intro X φ ψ h₁ h₂
    let p := fatJoinInl K (A ⨿ B) ≫ φ
    have hψ : fatJoinInl K (A ⨿ B) ≫ ψ = p := by
      have he := congrArg (fun z : fatJoin K A ⟶ X ↦ fatJoinInl K A ≫ z) h₁
      simpa only [← Category.assoc, fatJoinInl_map, Category.id_comp] using he.symm
    have hc : laxCosliceCurry φ rfl = laxCosliceCurry ψ hψ := by
      apply coprod.hom_ext
      · rw [← laxCosliceCurry_precomp, ← laxCosliceCurry_precomp]
        congr 1
      · rw [← laxCosliceCurry_precomp, ← laxCosliceCurry_precomp]
        congr 1
    simpa only [laxCosliceUncurry_curry] using congrArg laxCosliceUncurry hc
  · intro X b c hbc
    let p := fatJoinInl K A ≫ b
    have hc : fatJoinInl K B ≫ c = p := hbc.symm
    let F : A ⨿ B ⟶ laxCoslice p := coprod.desc (laxCosliceCurry b rfl) (laxCosliceCurry c hc)
    refine ⟨laxCosliceUncurry F, ?_, ?_⟩
    · rw [← laxCosliceUncurry_precomp]
      change laxCosliceUncurry.{u} ((coprod.inl : A ⟶ A ⨿ B) ≫ F) = b
      rw [coprod.inl_desc, laxCosliceUncurry_curry]
    · rw [← laxCosliceUncurry_precomp]
      change laxCosliceUncurry.{u} ((coprod.inr : B ⟶ A ⨿ B) ≫ F) = c
      rw [coprod.inr_desc, laxCosliceUncurry_curry]


end SerrePositivity.InfinityCategories
