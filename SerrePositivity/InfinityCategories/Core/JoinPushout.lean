module

public import SerrePositivity.InfinityCategories.Core.JoinLifting

/-!
概要：通常の join による二項の pushout の保存。
方針：slice と coslice の普遍性で貼り合わせを元の因子の pushout に移す。
規約：いずれの射にも単射性を要求しない。
使われ方：Kerodon Lemma 4.6.2.10 のセル分解による比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left の因子の pushout は、もう一方の因子との join 後も pushout。
方針：sliceOver の curry と uncurry で元の pushout の普遍性へ移す。
規約：任意の単体集合の pushout と固定因子 K を扱う。
使われ方：Kerodon Lemma 4.6.2.10 の貼り合わせ。 -/
lemma join_left_isPushout {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {t : C ⟶ D}
    (h : IsPushout f g r t) (K : SSet.{u}) :
    IsPushout (joinMap f (𝟙 K)) (joinMap g (𝟙 K))
      (joinMap r (𝟙 K)) (joinMap t (𝟙 K)) := by
  have hw : joinMap f (𝟙 K) ≫ joinMap r (𝟙 K) = joinMap g (𝟙 K) ≫ joinMap t (𝟙 K) := by
    simp only [← joinMap_comp, Category.id_comp, h.w]
  apply IsPushout.mk' hw
  · intro X φ ψ h₁ h₂
    let p := joinInr D K ≫ φ
    have hψ : joinInr D K ≫ ψ = p := by
      have he := congrArg (fun z : join B K ⟶ X ↦ joinInr B K ≫ z) h₁
      simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp] using he.symm
    have hc : sliceOverCurry φ rfl = sliceOverCurry ψ hψ := by
      apply h.hom_ext
      · rw [sliceOverCurry_precomp, sliceOverCurry_precomp]
        congr 1
      · rw [sliceOverCurry_precomp, sliceOverCurry_precomp]
        congr 1
    simpa only [sliceOverUncurry_curry] using congrArg sliceOverUncurry hc
  · intro X b c hbc
    let p := joinInr B K ≫ b
    have hc : joinInr C K ≫ c = p := by
      have he := congrArg (fun z : join A K ⟶ X ↦ joinInr A K ≫ z) hbc
      simpa only [← Category.assoc, joinInr_joinMap, Category.id_comp] using he.symm
    have hab : f ≫ sliceOverCurry b rfl = g ≫ sliceOverCurry c hc := by
      rw [sliceOverCurry_precomp, sliceOverCurry_precomp]
      congr 1
    let F := h.desc (sliceOverCurry b rfl) (sliceOverCurry c hc) hab
    refine ⟨sliceOverUncurry F, ?_, ?_⟩
    · rw [← sliceOverUncurry_precomp]
      change sliceOverUncurry (r ≫ F) = b
      rw [show r ≫ F = sliceOverCurry b rfl from h.inl_desc _ _ _, sliceOverUncurry_curry]
    · rw [← sliceOverUncurry_precomp]
      change sliceOverUncurry (t ≫ F) = c
      rw [show t ≫ F = sliceOverCurry c hc from h.inr_desc _ _ _, sliceOverUncurry_curry]

/-- 概要：right の因子の pushout は、もう一方の因子との join 後も pushout。
方針：sliceUnder の curry と uncurry で元の pushout の普遍性へ移す。
規約：任意の単体集合の pushout と固定因子 K を扱う。
使われ方：Kerodon Lemma 4.6.2.10 の貼り合わせ。 -/
lemma join_right_isPushout {A B C D : SSet.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {t : C ⟶ D}
    (h : IsPushout f g r t) (K : SSet.{u}) :
    IsPushout (joinMap (𝟙 K) f) (joinMap (𝟙 K) g)
      (joinMap (𝟙 K) r) (joinMap (𝟙 K) t) := by
  have hw : joinMap (𝟙 K) f ≫ joinMap (𝟙 K) r = joinMap (𝟙 K) g ≫ joinMap (𝟙 K) t := by
    simp only [← joinMap_comp, Category.id_comp, h.w]
  apply IsPushout.mk' hw
  · intro X φ ψ h₁ h₂
    let p := joinInl K D ≫ φ
    have hψ : joinInl K D ≫ ψ = p := by
      have he := congrArg (fun z : join K B ⟶ X ↦ joinInl K B ≫ z) h₁
      simpa only [← Category.assoc, joinInl_joinMap, Category.id_comp] using he.symm
    have hc : sliceUnderCurry φ rfl = sliceUnderCurry ψ hψ := by
      apply h.hom_ext
      · rw [sliceUnderCurry_precomp, sliceUnderCurry_precomp]
        congr 1
      · rw [sliceUnderCurry_precomp, sliceUnderCurry_precomp]
        congr 1
    simpa only [sliceUnderUncurry_curry] using congrArg sliceUnderUncurry hc
  · intro X b c hbc
    let p := joinInl K B ≫ b
    have hc : joinInl K C ≫ c = p := by
      have he := congrArg (fun z : join K A ⟶ X ↦ joinInl K A ≫ z) hbc
      simpa only [← Category.assoc, joinInl_joinMap, Category.id_comp] using he.symm
    have hab : f ≫ sliceUnderCurry b rfl = g ≫ sliceUnderCurry c hc := by
      rw [sliceUnderCurry_precomp, sliceUnderCurry_precomp]
      congr 1
    let F := h.desc (sliceUnderCurry b rfl) (sliceUnderCurry c hc) hab
    refine ⟨sliceUnderUncurry F, ?_, ?_⟩
    · rw [← sliceUnderUncurry_precomp]
      change sliceUnderUncurry (r ≫ F) = b
      rw [show r ≫ F = sliceUnderCurry b rfl from h.inl_desc _ _ _, sliceUnderUncurry_curry]
    · rw [← sliceUnderUncurry_precomp]
      change sliceUnderUncurry (t ≫ F) = c
      rw [show t ≫ F = sliceUnderCurry c hc from h.inr_desc _ _ _, sliceUnderUncurry_curry]

end SerrePositivity.InfinityCategories
