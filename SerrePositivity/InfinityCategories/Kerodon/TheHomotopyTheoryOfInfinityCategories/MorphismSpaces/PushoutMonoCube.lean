module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PushoutDisjoint

/-!
概要：単射に沿う pushout の比較の単射性。
方針：貼り合わせ部分の逆像が一致するとき、その補集合の単体を pushout 内で分離する。
規約：貼り合わせ部分と円柱側の正方形だけに pullback 性を要求する。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の単射保存。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：型の二つの pushout の比較は、貼り合わせ部分の逆像が一致すれば単射。
方針：貼り合わせ先とその補集合に分け、補集合の像を分離する。
規約：右の貼り合わせ先への射は任意。i'、b、c が単射である。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の次数ごとの単射性。 -/
lemma types_mono_of_pushout_cube {A B C D A' B' C' D' : Type u}
    {i : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    {i' : A' ⟶ B'} {g' : A' ⟶ C'} {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (h : IsPushout i g r s) (h' : IsPushout i' g' r' s') [Mono i']
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D') [Mono b] [Mono c]
    (hi : IsPullback i a b i') (hg : g ≫ c = a ≫ g')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s') : Mono d := by
  classical
  have hpb := Types.isPullback_of_isPushout h' ((mono_iff_injective i').mp inferInstance)
  have hc : Function.Injective c := (mono_iff_injective c).mp inferInstance
  have hb : Function.Injective b := (mono_iff_injective b).mp inferInstance
  have houter : IsPullback i g (b ≫ r') (c ≫ s') := by
    apply (Types.isPullback_iff _ _ _ _).2
    refine ⟨?_, ?_, ?_⟩
    · rw [← hr, ← hs, ← Category.assoc, ← Category.assoc, h.w]
    · intro x y he
      have : Mono i := hi.mono_fst_of_mono
      exact (mono_iff_injective i).mp inferInstance he.1
    · intro x y he
      obtain ⟨z, hz₁, hz₂⟩ := Types.exists_of_isPullback hpb (b x) (c y) he
      obtain ⟨w, hw₁, hw₂⟩ := Types.exists_of_isPullback hi x z hz₁.symm
      refine ⟨w, hw₁, hc ?_⟩
      have hw := ConcreteCategory.congr_hom hg w
      change c (g w) = g' (a w) at hw
      rw [hw₂, hz₂] at hw
      exact hw
  have : Mono (c ≫ s') := by
    have : Mono s' := Types.pushoutCocone_inr_mono_of_isColimit h'.isColimit
    infer_instance
  apply Types.mono_of_isPushout_of_isPullback h.flip houter.flip hs hr
  intro x y hx hy hxy
  let j : {x : B // x ∉ Set.range i} → B' := fun x ↦ b x.val
  have hj : Function.Injective j := fun x y he ↦ Subtype.ext (hb he)
  have hd : ∀ z (x : {x : B // x ∉ Set.range i}), i' z ≠ j x := by
    intro z x he
    obtain ⟨w, hw, _⟩ := Types.exists_of_isPullback hi x.val z he.symm
    exact x.property ⟨w, hw⟩
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pushout_inl_comp_injective_of_disjoint h' j hj hd
  exact congrArg Subtype.val (he (show r' (j ⟨x, hx⟩) = r' (j ⟨y, hy⟩) from hxy))

/-- 概要：単体集合の pushout の比較は、貼り合わせ部分の逆像が一致すれば単射。
方針：各次数で型の pushout の単射判定を適用する。
規約：i'、b、c が単射、i と a の正方形が pullback。比較射 a の単射性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の fat join の単射保存。 -/
lemma mono_of_pushout_cube {A B C D A' B' C' D' : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    {i' : A' ⟶ B'} {g' : A' ⟶ C'} {r' : B' ⟶ D'} {s' : C' ⟶ D'}
    (h : IsPushout i g r s) (h' : IsPushout i' g' r' s') [Mono i']
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D') [Mono b] [Mono c]
    (hi : IsPullback i a b i') (hg : g ≫ c = a ≫ g')
    (hr : r ≫ d = b ≫ r') (hs : s ≫ d = c ≫ s') : Mono d := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj n
  exact types_mono_of_pushout_cube (h.map ev) (h'.map ev)
    (a.app n) (b.app n) (c.app n) (d.app n) (hi.map ev)
    (congrArg (fun f ↦ f.app n) hg) (congrArg (fun f ↦ f.app n) hr)
    (congrArg (fun f ↦ f.app n) hs)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
