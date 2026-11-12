module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutMonoCube

/-!
概要：貼り合わせ部分と交わらない部分の pushout 後の逆像。
方針：型の pushout 上の分離関数で貼り合わせ部分の外の点を検出する。
規約：もう一方の貼り合わせ先の自然性の正方形の pullback 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の残った端点の逆像。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：型の pushout で貼り合わせ部分の外の点は円柱側の他の点と同一視されない。
方針：外の点を some、貼り合わせ部分を none にする分離関数を作る。
規約：貼り合わせる射の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の円柱の外側の検出。 -/
lemma types_eq_of_pushout_inl_eq_of_disjoint {A B C D T : Type u}
    {i : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (h : IsPushout i g r s) (j : T → B) (hd : ∀ a t, i a ≠ j t)
    (x : B) (t : T) (he : r x = r (j t)) : x = j t := by
  classical
  let f : B → Option B := fun x ↦ if x ∈ Set.range i then none else some x
  have hw : i ≫ (↾f) = g ≫ (↾fun _ ↦ (none : Option B)) := by
    apply ConcreteCategory.hom_ext
    intro a
    change (if i a ∈ Set.range i then none else some (i a)) = none
    exact if_pos ⟨a, rfl⟩
  obtain ⟨q, hq, _⟩ := h.exists_desc (↾f) (↾fun _ ↦ (none : Option B)) hw
  have hj : j t ∉ Set.range i := by rintro ⟨a, ha⟩; exact hd a t ha
  have hq₁ := ConcreteCategory.congr_hom hq x
  have hq₂ := ConcreteCategory.congr_hom hq (j t)
  have hh : f x = some (j t) := by
    change q (r x) = f x at hq₁
    change q (r (j t)) = f (j t) at hq₂
    rw [← hq₁, he, hq₂]
    exact if_neg hj
  dsimp [f] at hh
  split_ifs at hh with hx
  exact Option.some.inj hh

/-- 概要：型の pushout の貼り合わせ部分と交わらない単射の逆像は pushout 後も一致する。
方針：pushout の点を二つの像に分け、貼り合わせ部分の外の点を分離する。
規約：標的側の貼り合わせ射 i' は単射、j と j' の正方形が pullback。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の残った端点。 -/
lemma types_isPullback_pushout_inl_comp_of_disjoint
    {A B C D A' B' C' D' T T' : Type u}
    {i : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    {i' : A' ⟶ B'} {g' : A' ⟶ C'} {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (h : IsPushout i g r s) (h' : IsPushout i' g' r' s') [Mono i']
    (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (j : T ⟶ B) (j' : T' ⟶ B') [Mono j'] (z : T ⟶ T')
    (hJ : IsPullback j z b j')
    (hd : ∀ a t, i a ≠ j t) (hd' : ∀ a t, i' a ≠ j' t) :
    IsPullback (j ≫ r) z d (j' ≫ r') := by
  have : Mono j := hJ.mono_fst_of_mono
  have hj : Function.Injective (fun t ↦ r (j t)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushout_inl_comp_injective_of_disjoint h j ((mono_iff_injective j).mp inferInstance) hd
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, hr, ← Category.assoc, hJ.w, Category.assoc]
  · intro x y he
    exact hj he.1
  · intro x y he
    obtain (⟨w, rfl⟩ | ⟨w, rfl⟩) := Types.eq_or_eq_of_isPushout h x
    · have hw : r' (b w) = r' (j' y) := by
        simpa only [types_comp_apply] using
          ((ConcreteCategory.congr_hom hr w).symm.trans he)
      have hb := types_eq_of_pushout_inl_eq_of_disjoint h' j' hd' (b w) y hw
      obtain ⟨v, hv₁, hv₂⟩ := Types.exists_of_isPullback hJ w y hb
      exact ⟨v, by simpa only [types_comp_apply, hv₁], hv₂⟩
    · have hw : r' (j' y) = s' (c w) := by
        simpa only [types_comp_apply] using
          (he.symm.trans (ConcreteCategory.congr_hom hs w))
      have hp := Types.isPullback_of_isPushout h' ((mono_iff_injective i').mp inferInstance)
      obtain ⟨v, hv, _⟩ := Types.exists_of_isPullback hp (j' y) (c w) hw
      exact False.elim (hd' v y hv)

/-- 概要：単体集合の pushout の貼り合わせ部分と交わらない単射の逆像は pushout 後も一致する。
方針：各次数で型の pushout の逆像の計算を使う。
規約：標的側の貼り合わせ射 i' と j' は単射。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の一端の比較。 -/
lemma isPullback_pushout_inl_comp_of_disjoint
    {A B C D A' B' C' D' T T' : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    {i' : A' ⟶ B'} {g' : A' ⟶ C'} {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (h : IsPushout i g r s) (h' : IsPushout i' g' r' s') [Mono i']
    (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s')
    (j : T ⟶ B) (j' : T' ⟶ B') [Mono j'] (z : T ⟶ T')
    (hJ : IsPullback j z b j')
    (hd : ∀ n a t, i.app n a ≠ j.app n t) (hd' : ∀ n a t, i'.app n a ≠ j'.app n t) :
    IsPullback (j ≫ r) z d (j' ≫ r') := by
  have hw : (j ≫ r) ≫ d = z ≫ (j' ≫ r') := by
    rw [Category.assoc, hr, ← Category.assoc, hJ.w, Category.assoc]
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  apply evaluationJointlyReflectsLimits
  intro n
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  apply (isLimitMapConePullbackConeEquiv ev hw).2
  exact (types_isPullback_pushout_inl_comp_of_disjoint (h.map ev) (h'.map ev)
    (b.app n) (c.app n) (d.app n) (congrArg (fun f ↦ f.app n) hr)
    (congrArg (fun f ↦ f.app n) hs) (j.app n) (j'.app n) (z.app n)
    (hJ.map ev) (hd n) (hd' n)).isLimit

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
