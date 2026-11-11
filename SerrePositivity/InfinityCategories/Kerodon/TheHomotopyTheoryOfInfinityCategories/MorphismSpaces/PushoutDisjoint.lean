module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting

/-!
概要：貼り合わせる部分と交わらない部分の pushout 内での単射性。
方針：型の pushout の普遍性で分離関数を作り、各次数で適用する。
規約：貼り合わせ先の射に単射性を要求しない。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な区間による写像円柱。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：型の pushout では貼り合わせ部分と交わらない単射の像は保たれる。
方針：その部分の点を区別し、それ以外を none にする関数を pushout 上に延長する。
規約：貼り合わせる二つの射の単射性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の写像円柱の端点の単射性。 -/
lemma pushout_inl_comp_injective_of_disjoint {S X Y P T : Type u}
    {i : S ⟶ X} {f : S ⟶ Y} {k : X ⟶ P} {l : Y ⟶ P}
    (h : IsPushout i f k l) (j : T → X) (hj : Function.Injective j)
    (hd : ∀ s t, i s ≠ j t) : Function.Injective (fun t ↦ k (j t)) := by
  classical
  let a : X → Option T := Function.extend j some (fun _ ↦ none)
  have hw : i ≫ (↾a) = f ≫ (↾fun _ ↦ (none : Option T)) := by
    apply ConcreteCategory.hom_ext
    intro s
    change a (i s) = none
    apply Function.extend_apply'
    rintro ⟨t, ht⟩
    exact hd s t ht.symm
  obtain ⟨d, hk, _⟩ := h.exists_desc (↾a) (↾fun _ ↦ (none : Option T)) hw
  intro t t' ht
  have hk₀ : ∀ t, d (k (j t)) = some t := by
    intro t
    have he := ConcreteCategory.congr_hom hk (j t)
    change d (k (j t)) = a (j t) at he
    exact he.trans (hj.extend_apply some (fun _ ↦ none) t)
  have he := congrArg (fun p ↦ d p) ht
  rw [hk₀, hk₀] at he
  exact Option.some.inj he

/-- 概要：単体集合の pushout では貼り合わせ部分と各次数で交わらない単射は保たれる。
方針：評価関手が pushout を保つことと型での分離関数を使う。
規約：交わらない条件は全ての次数の単体について要求する。
使われ方：Kerodon §4.6.2（Tag 01HM） の可逆な写像円柱の単射性。 -/
lemma mono_pushout_inl_comp_of_disjoint {A B C D T : SSet.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {k : B ⟶ D} {l : C ⟶ D}
    (h : IsPushout i f k l) (j : T ⟶ B) [Mono j]
    (hd : ∀ n (a : A.obj n) (t : T.obj n), i.app n a ≠ j.app n t) : Mono (j ≫ k) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (mono_iff_injective _).2
  exact pushout_inl_comp_injective_of_disjoint
    (h.map ((evaluation SimplexCategoryᵒᵖ (Type u)).obj n)) (j.app n)
    ((mono_iff_injective _).mp inferInstance) (hd n)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
