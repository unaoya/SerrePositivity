module

public import SerrePositivity.KST.LocalizingInvariants.ProLevelwiseInverse

/-!
概要：指定した任意の深さ以降で、元の pro 同型の両三角形を持つ逆射を選ぶ。
方針：既存の逆の始域を元の塔の遷移で前合成する。
規約：元のレベル射と遷移を保持。使われ方：roof の段に合わせた係数逆の選択。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y : Tower C} (f : LevelHom X Y)

lemma exists_inverse_after (hf : IsProIso f) (i bound : ℕ) :
    ∃ m, ∃ hi : i ≤ m, bound ≤ m ∧ ∃ r : Y.obj m ⟶ X.obj i,
      f.app m ≫ r = X.transition hi ∧ r ≫ f.app i = Y.transition hi := by
  obtain ⟨j, hj, r, hl, hr⟩ := hf i
  let m := max j bound
  have hm : j ≤ m := le_max_left _ _
  refine ⟨m, hj.trans hm, le_max_right _ _, Y.transition hm ≫ r, ?_, ?_⟩
  · rw [← Category.assoc, ← f.naturality hm, Category.assoc, hl, X.transition_comp]
  · rw [Category.assoc, hr, Y.transition_comp]

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram
