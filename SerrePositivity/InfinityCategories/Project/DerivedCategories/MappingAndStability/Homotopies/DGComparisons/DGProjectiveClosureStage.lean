module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGProjectiveModuleFamily

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
def dgProjectiveFamilySum (F G : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  ⟨F.1 ⊕ G.1, fun i ↦ Sum.elim F.2 G.2 i⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgProjectiveFamilyUnion {T : Type u} (F : T → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  ⟨Σ a : T, (F a).1, fun i ↦ (F i.1).2 i.2⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
def dgProjectiveClosureStage {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) : T → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D :=
  wellFounded_lt.fix (fun a rec ↦ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyNext R D
    (dgProjectiveFamilySum R D F (dgProjectiveFamilyUnion R D
      (fun b : {b : T // b < a} ↦ rec b.val b.property))))

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureStage_eq {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) (a : T) :
    dgProjectiveClosureStage R D F a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgProjectiveFamilyNext R D
      (dgProjectiveFamilySum R D F (dgProjectiveFamilyUnion R D
        (fun b : {b : T // b < a} ↦ dgProjectiveClosureStage R D F b.val))) := by
  rw [dgProjectiveClosureStage, WellFounded.fix_eq]

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureStage_base {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) (a : T) (i : F.1) :
    ∃ j : (dgProjectiveClosureStage R D F a).1,
      (dgProjectiveClosureStage R D F a).2 j = F.2 i := by
  rw [dgProjectiveClosureStage_eq]
  exact ⟨.inr (.inl (.inl i)), rfl⟩

/-- 同じ実代表族の構成・閉性を保持する。 -/
lemma dgProjectiveClosureStage_lift {T : Type u} [LinearOrder T] [WellFoundedLT T]
    (F : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGProjectiveModuleFamily R D) {a b : T} (hab : a < b)
    (i : (dgProjectiveClosureStage R D F a).1) :
    ∃ j : (dgProjectiveClosureStage R D F b).1,
      (dgProjectiveClosureStage R D F b).2 j = (dgProjectiveClosureStage R D F a).2 i := by
  rw [dgProjectiveClosureStage_eq R D F b]
  exact ⟨.inr (.inl (.inr ⟨⟨a, hab⟩, i⟩)), rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
