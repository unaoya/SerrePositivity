module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveClosureStage

/-!
概要：正則非可算 κ の小さい射影的代表族を、実際の加群演算で閉じる。
方針：小さい超限段階と可算個の段階の狭義上界で、同じ代表族の閉性を証明する。
規約：全同型コピーを集めず、全共変 Hom の κ-compact 性は別に証明する。
使われ方：K-7 の実 dg 小模型への対象・小ささ・射影性・直和閉性の供給。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgProjectiveClosureFamily {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyUnion R D (fun a : T ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a)

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_base {T : Type u} [LinearOrder T] [WellFoundedLT T]
    [Nonempty T] (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) (i : F.1) :
    ∃ j : (dgProjectiveClosureFamily R D (T := T) F).1,
      (dgProjectiveClosureFamily R D (T := T) F).2 j = F.2 i := by
  obtain ⟨j, hj⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_base R D F (Classical.arbitrary T) i
  exact ⟨⟨Classical.arbitrary T, j⟩, hj⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_zero {T : Type u} [LinearOrder T] [WellFoundedLT T]
    [Nonempty T] (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) :
    ∃ j : (dgProjectiveClosureFamily R D (T := T) F).1,
      ((dgProjectiveClosureFamily R D (T := T) F).2 j).val = moduleZero R D := by
  suffices h : ∃ j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F (Classical.arbitrary T)).1,
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F (Classical.arbitrary T)).2 j).val =
        moduleZero R D by
    obtain ⟨j, hj⟩ := h
    exact ⟨⟨Classical.arbitrary T, j⟩, hj⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F (Classical.arbitrary T)]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyNext_zero R D _

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_shift {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b) (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)
    (s : ℤ) (i : (dgProjectiveClosureFamily R D (T := T) F).1) :
    ∃ j : (dgProjectiveClosureFamily R D (T := T) F).1,
      ((dgProjectiveClosureFamily R D (T := T) F).2 j).val =
        ((dgProjectiveClosureFamily R D (T := T) F).2 i).val⟦s⟧ := by
  obtain ⟨b, hb⟩ := hT (fun _ ↦ i.1)
  suffices h : ∃ j : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).1,
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).2 j).val =
        ((dgProjectiveClosureFamily R D (T := T) F).2 i).val⟦s⟧ by
    obtain ⟨j, hj⟩ := h
    exact ⟨⟨b, j⟩, hj⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F b]
  exact ⟨.inr (.inr (.inl (s, .inr ⟨⟨i.1, hb 0⟩, i.2⟩))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_binary {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b) (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)
    (i j : (dgProjectiveClosureFamily R D (T := T) F).1) :
    ∃ k : (dgProjectiveClosureFamily R D (T := T) F).1,
      ((dgProjectiveClosureFamily R D (T := T) F).2 k).val =
        (((dgProjectiveClosureFamily R D (T := T) F).2 i).val ⨿
          ((dgProjectiveClosureFamily R D (T := T) F).2 j).val) := by
  obtain ⟨b, hb⟩ := hT (fun _ ↦ max i.1 j.1)
  have hi : i.1 < b := lt_of_le_of_lt (le_max_left _ _) (hb 0)
  have hj : j.1 < b := lt_of_le_of_lt (le_max_right _ _) (hb 0)
  suffices h : ∃ k : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).1,
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).2 k).val =
        (((dgProjectiveClosureFamily R D (T := T) F).2 i).val ⨿
          ((dgProjectiveClosureFamily R D (T := T) F).2 j).val) by
    obtain ⟨k, hk⟩ := h
    exact ⟨⟨b, k⟩, hk⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F b]
  exact ⟨.inr (.inr (.inr (.inl
    (.inr ⟨⟨i.1, hi⟩, i.2⟩, .inr ⟨⟨j.1, hj⟩, j.2⟩)))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_cone {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b) (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)
    (i j : (dgProjectiveClosureFamily R D (T := T) F).1)
    (f : ((dgProjectiveClosureFamily R D (T := T) F).2 i).val ⟶
      ((dgProjectiveClosureFamily R D (T := T) F).2 j).val) :
    ∃ k : (dgProjectiveClosureFamily R D (T := T) F).1,
      ((dgProjectiveClosureFamily R D (T := T) F).2 k).val = moduleCone R D f := by
  obtain ⟨b, hb⟩ := hT (fun _ ↦ max i.1 j.1)
  have hi : i.1 < b := lt_of_le_of_lt (le_max_left _ _) (hb 0)
  have hj : j.1 < b := lt_of_le_of_lt (le_max_right _ _) (hb 0)
  suffices h : ∃ k : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).1,
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).2 k).val = moduleCone R D f by
    obtain ⟨k, hk⟩ := h
    exact ⟨⟨b, k⟩, hk⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F b]
  exact ⟨.inr (.inr (.inr (.inr (.inl
    ⟨.inr ⟨⟨i.1, hi⟩, i.2⟩, .inr ⟨⟨j.1, hj⟩, j.2⟩, f⟩)))), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureFamily_countable {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (hT : ∀ s : ℕ → T, ∃ b, ∀ n, s n < b) (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D)
    (i : ℕ → (dgProjectiveClosureFamily R D (T := T) F).1) :
    ∃ k : (dgProjectiveClosureFamily R D (T := T) F).1,
      ((dgProjectiveClosureFamily R D (T := T) F).2 k).val =
        ∐ (fun n : ℕ ↦ ((dgProjectiveClosureFamily R D (T := T) F).2 (i n)).val) := by
  obtain ⟨b, hb⟩ := hT (fun n ↦ (i n).1)
  suffices h : ∃ k : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).1,
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F b).2 k).val =
        ∐ (fun n : ℕ ↦ ((dgProjectiveClosureFamily R D (T := T) F).2 (i n)).val) by
    obtain ⟨k, hk⟩ := h
    exact ⟨⟨b, k⟩, hk⟩
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F b]
  exact ⟨.inr (.inr (.inr (.inr (.inr
    (fun n ↦ .inr ⟨⟨(i n).1, hb n⟩, (i n).2⟩))))), rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
