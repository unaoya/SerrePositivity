module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.MorphismInitialTailHom
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.SimplicialHomConstantIdentity

/-!
概要：元の初点固定 tail の初点 Hom を、元の恒等射と元の射へ正規化する。
方針：元の二時刻ラベルの計算を実 Hom に適用する。
規約：元の実 path を保持。使われ方：同じ固定射の二つの全 prism の初点 Hom の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y : C}

/-- 時刻零への実初点 Hom は、元の始域の恒等。 -/
lemma morphismInitialTail_head_zero (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    (morphismInitialTail f α).val.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (morphismInitialTail_obj_zero f α j hj)) = toUnit _ ≫ eId SSet X := by
  rw [← simplicialHom_const_id]
  exact morphismInitialTail_map_labels f α (ULift.up 0) (ULift.up j.succ)
    (show (0 : Fin (n + 2)) ≤ j.succ from Fin.zero_le _) 0 0 rfl hj (by decide)

/-- 時刻一への実初点 Hom は、元の指定射。 -/
lemma morphismInitialTail_head_one (f : X ⟶ Y) {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    (morphismInitialTail f α).val.map ⟨ULift.up 0⟩ ⟨ULift.up j.succ⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (morphismInitialTail_obj_one f α j hj)) =
      SSet.const (SimplicialCategory.homEquiv' X Y f) := by
  exact morphismInitialTail_map_labels f α (ULift.up 0) (ULift.up j.succ)
    (show (0 : Fin (n + 2)) ≤ j.succ from Fin.zero_le _) 0 1 rfl hj (by decide)

end SerrePositivity.InfinityCategories.F2
