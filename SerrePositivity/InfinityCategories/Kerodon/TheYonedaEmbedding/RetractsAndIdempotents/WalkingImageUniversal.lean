module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.TriangleKernel
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingAbsorption
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification

/-!
概要：元の分裂添字では、元の分裂対象は始対象かつ終対象。
方針：両端の片方が元の分裂対象なら、元の射は吸収射だけであると分類する。
規約：元の分裂対象と指定した元の射を使う。
使われ方：強い分裂の余錐・錐と cofinality の検査。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の分裂対象から出る元の射は、元の吸収射に限る。 -/
lemma walkingHom_from_image {P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage ⟶ P) :
    f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingHom_cases f with h | ⟨h, _, _⟩
  · exact h
  · exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource_ne_image h.symm)

/-- 元の分裂対象へ入る元の射も、元の吸収射に限る。 -/
lemma walkingHom_to_image {P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) :
    f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _ _ := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingHom_cases f with h | ⟨_, h, _⟩
  · exact h
  · exact False.elim (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource_ne_image h.symm)

/-- 元の分裂対象は、元の分裂添字の始対象。 -/
def walkingImage_isInitial : IsInitial _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} :=
  IsInitial.ofUniqueHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage) (fun _ f ↦ walkingHom_from_image f)

/-- 元の分裂対象は、元の分裂添字の終対象。 -/
def walkingImage_isTerminal : IsTerminal _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} :=
  IsTerminal.ofUniqueHom (fun P ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom P _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage)
    (fun _ f ↦ walkingHom_to_image f)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
