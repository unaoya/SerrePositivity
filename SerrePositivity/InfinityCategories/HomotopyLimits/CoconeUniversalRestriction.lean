module

public import SerrePositivity.InfinityCategories.HomotopyLimits.IteratedSliceUnderRestriction
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
public import SerrePositivity.InfinityCategories.Core.Cocone

/-!
概要：余極限余錐全体から元の底図式への coslice 制限の自明 Kan 性。
方針：元の固定図式と可変終点を同じ join の再結合で保持する。
規約：充填条件を追加仮定しない。使われ方：HTT 5.5.4 の局所同値の pushout 保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 反復 coslice の射影が自明 Kan 射なら元の図式への制限もそうである。 -/
lemma uncurriedSliceUnderRestriction_trivial {K L X : SSet.{u}} {p : K ⟶ X}
    (q : L ⟶ sliceUnder p) [TrivialKanFibration (sliceUnderProjection q)] :
    TrivialKanFibration (uncurriedSliceUnderRestriction q) := by
  constructor
  rw [← trivialKanFibrations.cancel_left_of_respectsIso (iteratedSliceUnderIso q).hom,
    iteratedSliceUnderIso_restriction]
  exact TrivialKanFibration.mem (p := sliceUnderProjection q)

/-- 余極限余錐全体から元の底図式への coslice 制限は自明 Kan 射。 -/
lemma sliceUnderRestrict_cocone_trivial {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    TrivialKanFibration (sliceUnderRestrict c.val (joinInl K (Δ[0] : SSet.{u}))) := by
  let q := (SSet.yonedaEquiv (X := sliceUnder p) (n := ⦋0⦌)).symm c
  have : TrivialKanFibration (sliceUnderProjection q) :=
    (isInitialVertex_iff_trivialKanFibration (X := sliceUnder p) c).mp hc
  have h := uncurriedSliceUnderRestriction_trivial q
  have hr : trivialKanFibrations
      (sliceUnderRestrict (sliceUnderUncurry q) (joinInl K (Δ[0] : SSet.{u}))) :=
    (trivialKanFibrations.cancel_right_of_respectsIso _
      (eqToHom (congrArg (fun f : K ⟶ X ↦ sliceUnder f)
        (sliceUnderUncurry_fixed q)))).mp h.mem
  have hp : sliceUnderUncurry q = c.val := sliceUnderUncurry_yoneda 0 c
  constructor
  rw [hp] at hr
  exact hr

end SerrePositivity.InfinityCategories.HomotopyLimits
