module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingAbsorption

/-!
概要：元の分裂添字の対象と射を、二対象と吸収射により分類する。
方針：元の二元モノイドの分類と Karoubi の射の両側条件を使う。
規約：対象の等式と元の射の値を保持し、同型類だけに置き換えない。
使われ方：元の交互セルの像による分裂添字の全被覆性。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の一対象圏の対象は、指定した元の対象そのもの。 -/
lemma walkingObject_eq (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}) : P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject := by
  cases P with | up P => cases P; rfl

/-- 元の射の値は、恒等元か指定した吸収元。 -/
lemma walkingScalar_cases (a : WithOne PUnit.{u + 1}) :
    a = 1 ∨ a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorber := by
  cases a using WithOne.recOneCoe with
  | one => exact Or.inl rfl
  | coe a => cases a; exact Or.inr rfl

/-- 元の分裂添字の対象は、指定した非分裂対象か分裂対象そのもの。 -/
lemma walkingSplit_object_cases (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) :
    P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ∨ P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage := by
  obtain ⟨P, p, hp⟩ := P
  obtain rfl := walkingObject_eq P
  rcases walkingScalar_cases (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar p) with h | h
  · left
    change p = 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingObject at h
    cases h
    rfl
  · right
    change p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent at h
    cases h
    rfl

/-- 元の対象が非分裂対象であることと、元の冪等元の値が恒等であることは同値。 -/
lemma walkingSplit_source_iff (P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) :
    P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar P.p = 1 := by
  constructor
  · rintro rfl
    rfl
  · intro h
    rcases walkingSplit_object_cases P with he | he
    · exact he
    · subst P
      exact False.elim (WithOne.coe_ne_one h)

/-- 元の射の値が恒等なら、その両端は同じ指定非分裂対象。 -/
lemma walkingHom_one_endpoints {P Q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : P ⟶ Q)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f = 1) : P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ∧ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource := by
  have hp := CategoryTheory.Idempotents.Karoubi.p_comp f
  have hq := CategoryTheory.Idempotents.Karoubi.comp_p f
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f * _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar P.p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f at hp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar Q.p * _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f at hq
  rw [h, one_mul] at hp
  rw [h, mul_one] at hq
  exact ⟨(walkingSplit_source_iff P).mpr hp, (walkingSplit_source_iff Q).mpr hq⟩

/-- 元の射は吸収射か、両端が非分裂対象で値が恒等の射。 -/
lemma walkingHom_cases {P Q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : P ⟶ Q) :
    f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom P Q ∨
      P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ∧ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f = 1 := by
  rcases walkingScalar_cases (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.f) with h | h
  · exact Or.inr ⟨(walkingHom_one_endpoints f h).1, (walkingHom_one_endpoints f h).2, h⟩
  · exact Or.inl (CategoryTheory.Idempotents.Karoubi.Hom.ext h)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
