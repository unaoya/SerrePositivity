module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking

/-!
概要：元の分裂添字の全対象間で、非恒等の指定冪等元による吸収射を構成する。
方針：二元モノイドの元の冪等元の左右吸収則を、形式的像の射へ移す。
規約：恒等射と元の吸収射を区別し、元の包含・射影をそのまま回収する。
使われ方：Ret の濾過に使う元の交互列の全射の構成。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の二元モノイドの、元の非恒等冪等元。 -/
def walkingAbsorber : WithOne PUnit.{u + 1} := ↑PUnit.unit

/-- 元の冪等元の左吸収則。 -/
lemma walkingAbsorber_mul (a : WithOne PUnit.{u + 1}) :
    walkingAbsorber * a = walkingAbsorber := by
  cases a using WithOne.recOneCoe with
  | one => rfl
  | coe a => cases a; rfl

/-- 元の冪等元の右吸収則。 -/
lemma mul_walkingAbsorber (a : WithOne PUnit.{u + 1}) :
    a * walkingAbsorber = walkingAbsorber := by
  cases a using WithOne.recOneCoe with
  | one => rfl
  | coe a => cases a; rfl

/-- 元の一対象圏の射を、同じ元の二元モノイドの元として表示する。 -/
def walkingScalar {P Q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}} (f : P ⟶ Q) : WithOne PUnit.{u + 1} := f

/-- 元の任意の二つの形式的像の間の、元の冪等元で指定した射。 -/
def walkingAbsorbingHom (P Q : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}) : P ⟶ Q :=
  ⟨walkingAbsorber, by
    change (walkingScalar Q.p * walkingAbsorber) * walkingScalar P.p = walkingAbsorber
    rw [mul_walkingAbsorber, walkingAbsorber_mul]⟩

/-- 元の吸収射の後に元の任意の射を合成しても、同じ吸収射。 -/
lemma walkingAbsorbingHom_comp {P Q R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : Q ⟶ R) :
    walkingAbsorbingHom P Q ≫ f = walkingAbsorbingHom P R := by
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  change walkingScalar f.f * walkingAbsorber = walkingAbsorber
  exact mul_walkingAbsorber f.f

/-- 元の任意の射の後に元の吸収射を合成しても、同じ吸収射。 -/
lemma comp_walkingAbsorbingHom {P Q R : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingSplit.{u}} (f : P ⟶ Q) :
    f ≫ walkingAbsorbingHom Q R = walkingAbsorbingHom P R := by
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  change walkingAbsorber * walkingScalar f.f = walkingAbsorber
  exact walkingAbsorber_mul f.f

/-- 分裂対象での同じ吸収射は、その元の恒等射。 -/
lemma walkingAbsorbingHom_image :
    walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage = 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage := rfl

/-- 元の吸収射は、分裂対象から元の非分裂対象への同じ包含を回収する。 -/
lemma walkingAbsorbingHom_section :
    walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSection := rfl

/-- 元の吸収射は、非分裂対象から元の分裂対象への同じ射影を回収する。 -/
lemma walkingAbsorbingHom_retraction :
    walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetraction := rfl

/-- 元の非分裂対象での同じ吸収射は、元の非恒等冪等元の像。 -/
lemma walkingAbsorbingHom_idempotent :
    walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingIdempotent := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
