module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingClassification
public import Mathlib.CategoryTheory.Category.Cat

/-!
概要：元の二元冪等モノイドの可換性から、元の Idem 添字と反対圏の同型を作る。
方針：元の射の値を保ち、元の合成順序の反転を可換性で照合する。
規約：元の対象と元の指定冪等元をそのまま使う。
使われ方：極限から強い分裂への逆方向の厳密な双対化。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の二元冪等モノイドの元は互いに可換。 -/
lemma walkingScalar_mul_comm (a b : WithOne PUnit.{u + 1}) : a * b = b * a := by
  rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar_cases a with h | h
  · rw [h, one_mul, mul_one]
  · rw [h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorber_mul, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mul_walkingAbsorber]

/-- 元の三つの射の値の積は、端の二値を交換しても同じ。 -/
lemma walkingScalar_reverse_triple (a b c : WithOne PUnit.{u + 1}) :
    (a * b) * c = (c * b) * a := by
  rw [mul_assoc, walkingScalar_mul_comm b c, ← mul_assoc, walkingScalar_mul_comm a c,
    mul_assoc, walkingScalar_mul_comm a b, ← mul_assoc]

/-- 元の Idem の各射の値を保つ、元の反対圏への関手。 -/
def walkingIdemToOpposite : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}ᵒᵖ where
  obj P := Opposite.op P
  map {P Q} f := (show Q ⟶ P from _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f).op
  map_id _ := rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar g * _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f * _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar g
    exact walkingScalar_mul_comm _ _

/-- 元の反対 Idem の各射の値を保つ、元の Idem への関手。 -/
def walkingIdemFromOpposite : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}ᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} where
  obj P := P.unop
  map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.unop
  map_id _ := rfl
  map_comp f g := walkingScalar_mul_comm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar f.unop) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingScalar g.unop)

/-- 元の全 Idem と元の反対圏の、元の射の値を保つ圏同型。 -/
def walkingIdemOppositeIso : Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ≅ Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u}ᵒᵖ where
  hom := walkingIdemToOpposite.toCatHom
  inv := walkingIdemFromOpposite.toCatHom
  hom_inv_id := by apply Cat.Hom.ext; rfl
  inv_hom_id := by apply Cat.Hom.ext; rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
