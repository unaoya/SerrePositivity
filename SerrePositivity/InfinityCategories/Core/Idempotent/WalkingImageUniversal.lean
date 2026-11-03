module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Core.Idempotent.TriangleKernel
public import SerrePositivity.InfinityCategories.Core.Idempotent.Walking
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingAbsorption
public import SerrePositivity.InfinityCategories.Core.Idempotent.WalkingClassification

/-!
概要：元の分裂添字では、元の分裂対象は始対象かつ終対象。
方針：両端の片方が元の分裂対象なら、元の射は吸収射だけであると分類する。
規約：元の分裂対象と指定した元の射を使う。
使われ方：強い分裂の余錐・錐と cofinality の検査。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の分裂対象から出る元の射は、元の吸収射に限る。 -/
lemma walkingHom_from_image {P : WalkingSplit.{u}} (f : walkingImage ⟶ P) :
    f = walkingAbsorbingHom _ _ := by
  rcases walkingHom_cases f with h | ⟨h, _, _⟩
  · exact h
  · exact False.elim (walkingSource_ne_image h.symm)

/-- 元の分裂対象へ入る元の射も、元の吸収射に限る。 -/
lemma walkingHom_to_image {P : WalkingSplit.{u}} (f : P ⟶ walkingImage) :
    f = walkingAbsorbingHom _ _ := by
  rcases walkingHom_cases f with h | ⟨_, h, _⟩
  · exact h
  · exact False.elim (walkingSource_ne_image h.symm)

/-- 元の分裂対象は、元の分裂添字の始対象。 -/
def walkingImage_isInitial : IsInitial walkingImage.{u} :=
  IsInitial.ofUniqueHom (walkingAbsorbingHom walkingImage) (fun _ f ↦ walkingHom_from_image f)

/-- 元の分裂対象は、元の分裂添字の終対象。 -/
def walkingImage_isTerminal : IsTerminal walkingImage.{u} :=
  IsTerminal.ofUniqueHom (fun P ↦ walkingAbsorbingHom P walkingImage)
    (fun _ f ↦ walkingHom_to_image f)

end SerrePositivity.InfinityCategories.F2.Idempotent
