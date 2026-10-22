module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingIdemOpposite

/-!
概要：元の分裂添字と元の反対圏を、元の二対象と全射の値を保って同型にする。
方針：元の Karoubi 射の両側条件を可換性で反転し、元の包含と照合する。
規約：元の射影と包含の反転は、元の同じ射の値で指定する。
使われ方：元の Idem 図式の強い分裂を、二重反転後に厳密に回収する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の Karoubi 射の値を保ち、その両端を反転する。 -/
def walkingReverseHom {P Q : WalkingSplit.{u}} (f : P ⟶ Q) : Q ⟶ P :=
  ⟨f.f, by
    change (walkingScalar P.p * walkingScalar f.f) * walkingScalar Q.p = walkingScalar f.f
    exact (walkingScalar_reverse_triple _ _ _).trans f.comm⟩

/-- 元の二射の合成の反転は、元の反転した二射の逆順の合成。 -/
lemma walkingReverseHom_comp {P Q R : WalkingSplit.{u}} (f : P ⟶ Q) (g : Q ⟶ R) :
    walkingReverseHom (f ≫ g) = walkingReverseHom g ≫ walkingReverseHom f := by
  apply CategoryTheory.Idempotents.Karoubi.Hom.ext
  exact walkingScalar_mul_comm _ _

/-- 元の分裂添字から元の反対圏への、元の全対象と射の値を保つ関手。 -/
def walkingSplitToOpposite : WalkingSplit.{u} ⥤ WalkingSplit.{u}ᵒᵖ where
  obj P := Opposite.op P
  map f := (walkingReverseHom f).op
  map_id _ := rfl
  map_comp f g := congrArg Quiver.Hom.op (walkingReverseHom_comp f g)

/-- 元の反対分裂添字から元の分裂添字への、元の全対象と射の値を保つ関手。 -/
def walkingSplitFromOpposite : WalkingSplit.{u}ᵒᵖ ⥤ WalkingSplit.{u} where
  obj P := P.unop
  map f := walkingReverseHom f.unop
  map_id _ := rfl
  map_comp f g := walkingReverseHom_comp g.unop f.unop

/-- 元の全分裂添字と元の反対圏の、元の対象と射の値を保つ圏同型。 -/
def walkingSplitOppositeIso : Cat.of WalkingSplit.{u} ≅ Cat.of WalkingSplit.{u}ᵒᵖ where
  hom := walkingSplitToOpposite.toCatHom
  inv := walkingSplitFromOpposite.toCatHom
  hom_inv_id := by apply Cat.Hom.ext; rfl
  inv_hom_id := by apply Cat.Hom.ext; rfl

/-- 元の包含と元の反転関手の正方形は、全対象・全射で厳密に可換。 -/
lemma walkingInclusion_toOpposite :
    walkingInclusion ⋙ walkingSplitToOpposite.{u} =
      walkingIdemToOpposite ⋙ walkingInclusion.op := rfl

end SerrePositivity.InfinityCategories.F2.Idempotent
