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
lemma dgProjectiveFamilyNext_property (P : ModuleCategory R D → Prop)
    (hzero : P (moduleZero R D))
    (hshift : ∀ M, P M → ∀ s : ℤ, P (M⟦s⟧))
    (hbinary : ∀ M N, P M → P N → P (M ⨿ N))
    (hcone : ∀ M N, P M → P N → ∀ f : M ⟶ N, P (moduleCone R D f))
    (hcountable : ∀ M : ℕ → ModuleCategory R D, (∀ n, P (M n)) → P (∐ M))
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) (hF : ∀ i, P ((F.2 i).val))
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyNext R D F).1) :
    P (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyNext R D F).2 i).val) := by
  rcases i with _ | i | ⟨s, i⟩ | ⟨i, j⟩ | ⟨i, j, f⟩ | i
  · exact hzero
  · exact hF i
  · exact hshift _ (hF i) s
  · exact hbinary _ _ (hF i) (hF j)
  · exact hcone _ _ (hF i) (hF j) f
  · exact hcountable _ (fun n ↦ hF (i n))

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureStage_property {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (P : ModuleCategory R D → Prop)
    (hzero : P (moduleZero R D))
    (hshift : ∀ M, P M → ∀ s : ℤ, P (M⟦s⟧))
    (hbinary : ∀ M N, P M → P N → P (M ⨿ N))
    (hcone : ∀ M N, P M → P N → ∀ f : M ⟶ N, P (moduleCone R D f))
    (hcountable : ∀ M : ℕ → ModuleCategory R D, (∀ n, P (M n)) → P (∐ M))
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) (hF : ∀ i, P ((F.2 i).val))
    (a : T) (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).1) :
    P (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).2 i).val) := by
  suffices h : ∀ a : T, ∀ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).1,
      P (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).2 i).val) from h a i
  intro a
  refine (wellFounded_lt (α := T)).induction
    (C := fun a ↦ ∀ i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).1,
      P (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage R D F a).2 i).val)) a ?_
  intro a ih
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveClosureStage_eq R D F a]
  apply dgProjectiveFamilyNext_property R D P hzero hshift hbinary hcone hcountable
  intro j
  rcases j with j | ⟨⟨b, hb⟩, j⟩
  · exact hF j
  · exact ih b hb j

end SerrePositivity.InfinityCategories.Project.DerivedCategories
