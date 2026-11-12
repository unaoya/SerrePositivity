module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCutSigmaReindex
/-!
概要：条件付き和を未選択内部点の実部分型上の和へ移す。
方針：同じ集合・点・cochain を保つ実添字比較を使う。
規約：元の全次数で同定する。使われ方：全次元 HA の右辺の照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open scoped BigOperators
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveDite_sum {α : Type u} [Fintype α] (p : α → Prop) [DecidablePred p]
    {M : Type v} [AddCommMonoid M] (f : ∀ x, p x → M) :
    (∑ x : α, if h : p x then f x h else 0) = ∑ x : {x // p x}, f x.val x.property := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun x => if h : p x then f x h else 0)
  have hp : (∑ x : {x // p x}, if h : p x.val then f x.val h else 0) =
      ∑ x : {x // p x}, f x.val x.property := by
    apply Finset.sum_congr rfl
    intro x _
    rw [dite_eq_left x.property]
  have hn : (∑ x : {x // ¬p x}, if h : p x.val then f x.val h else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [dite_eq_right x.property]
  rw [hp, hn, add_zero] at h
  exact h.symm
/-- 元の全添字と同じ実境界成分の比較。 -/
def dgNerveInteriorUnselectedEquiv {α : Type u} [LinearOrder α]
    (I S : Finset α) (a b : α) :
    {j : I // a < j.val ∧ j.val < b ∧ j.val ∉ S} ≃
      {j : α // j ∈ I.filter (fun x => a < x ∧ x < b) ∧ j ∉ S} where
  toFun p := ⟨p.val.val, Finset.mem_filter.mpr
    ⟨p.val.property, p.property.1, p.property.2.1⟩, p.property.2.2⟩
  invFun p := ⟨⟨p.val, (Finset.mem_filter.mp p.property.1).1⟩,
    (Finset.mem_filter.mp p.property.1).2.1,
    (Finset.mem_filter.mp p.property.1).2.2, p.property.2⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Subtype.ext; rfl
/-- 元の全添字と同じ実境界成分の比較。 -/
lemma dgNerveInteriorUnselected_sum {α : Type u} [Fintype α] [LinearOrder α]
    (I S : Finset α) (a b : α) {M : Type v} [AddCommMonoid M]
    (f : ∀ j, j ∈ I → a < j → j < b → j ∉ S → M) :
    (∑ j : I, if h : a < j.val ∧ j.val < b ∧ j.val ∉ S then
      f j.val j.property h.1 h.2.1 h.2.2 else 0) =
    ∑ j : {j : α // j ∈ I.filter (fun x => a < x ∧ x < b) ∧ j ∉ S},
      f j.val (Finset.mem_filter.mp j.property.1).1
        (Finset.mem_filter.mp j.property.1).2.1
        (Finset.mem_filter.mp j.property.1).2.2 j.property.2 := by
  rw [dgNerveDite_sum]
  exact Equiv.sum_comp (dgNerveInteriorUnselectedEquiv I S a b) (fun j =>
    f j.val (Finset.mem_filter.mp j.property.1).1
      (Finset.mem_filter.mp j.property.1).2.1
      (Finset.mem_filter.mp j.property.1).2.2 j.property.2)

/-- 内部点の条件付き和と同じ実内部点上の和の比較。 -/
lemma dgNerveInterior_sum {α : Type u} [LinearOrder α]
    (I : Finset α) (a b : α) {M : Type v} [AddCommMonoid M]
    (f : ∀ j, j ∈ I → a < j → j < b → M) :
    (∑ j : I, if h : a < j.val ∧ j.val < b then
      f j.val j.property h.1 h.2 else 0) =
    ∑ j : I.filter (fun x => a < x ∧ x < b),
      f j.val (Finset.mem_filter.mp j.property).1
        (Finset.mem_filter.mp j.property).2.1 (Finset.mem_filter.mp j.property).2.2 := by
  let T := I.filter (fun x => a < x ∧ x < b)
  let e : {j : I // a < j.val ∧ j.val < b} ≃ T :=
    { toFun := fun j => ⟨j.val.val, Finset.mem_filter.mpr ⟨j.val.property, j.property⟩⟩
      invFun := fun j => ⟨⟨j.val, (Finset.mem_filter.mp j.property).1⟩,
        (Finset.mem_filter.mp j.property).2⟩
      left_inv := fun j => by apply Subtype.ext; rfl
      right_inv := fun j => by apply Subtype.ext; rfl }
  rw [dgNerveDite_sum]
  exact Equiv.sum_comp e (fun j => f j.val (Finset.mem_filter.mp j.property).1
    (Finset.mem_filter.mp j.property).2.1 (Finset.mem_filter.mp j.property).2.2)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
