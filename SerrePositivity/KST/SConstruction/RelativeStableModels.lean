module
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryFunctor
public import SerrePositivity.KST.SConstruction.RelativeCofiberModel

/-! # 相対加法性の安定な入力の圏
概要：小安定圏 C と二つの閉じた全部分圏 A/B を束ね、その両条件を保つ完全関手を射にする。
方針：射は周囲の完全関手の部分型とし、両端の制限を関手化する。
規約：零対象や cofiber の選択を指定しない。使われ方：相対加法性の自然変換。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 相対入力は周囲の安定圏と二つの閉じた安定な頂点条件。 -/
structure RelativeStableModel where
  /-- 周囲の小安定圏。 -/
  ambient : StableModel.{u}
  /-- subobject が入る閉じた全部分圏の条件。 -/
  left : ClosedStablePredicate ambient
  /-- quotient が入る閉じた全部分圏の条件。 -/
  right : ClosedStablePredicate ambient

/-- 相対入力の射は両端の条件を保つ周囲の完全関手。 -/
instance relativeStableModelCategory : Category.{u} RelativeStableModel.{u} where
  Hom X Y := {f : X.ambient ⟶ Y.ambient //
    (∀ x, X.left.predicate x → Y.left.predicate (f.val.app (Opposite.op ⦋0⦌) x)) ∧
    (∀ x, X.right.predicate x → Y.right.predicate (f.val.app (Opposite.op ⦋0⦌) x))}
  id _ := ⟨𝟙 _, ⟨fun _ hx => hx, fun _ hx => hx⟩⟩
  comp f g := ⟨f.val ≫ g.val,
    ⟨fun x hx => g.property.1 _ (f.property.1 x hx),
      fun x hx => g.property.2 _ (f.property.2 x hx)⟩⟩
  id_comp f := Subtype.ext (Category.id_comp f.val)
  comp_id f := Subtype.ext (Category.comp_id f.val)
  assoc f g h := Subtype.ext (Category.assoc f.val g.val h.val)

/-- 相対入力から周囲の安定圏への忘却関手。 -/
def relativeAmbientFunctor : RelativeStableModel.{u} ⥤ StableModel.{u} where
  obj X := X.ambient
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- 相対入力の subobject 側の全部分圏を与える関手。 -/
def relativeLeftFunctor : RelativeStableModel.{u} ⥤ StableModel.{u} where
  obj X := closedStableModel X.left
  map {X Y} f := closedStableMap X.left Y.left f.val f.property.1
  map_id X := closedStableMap_id X.left
  map_comp {X Y Z} f g := closedStableMap_comp X.left Y.left Z.left f.val g.val
    f.property.1 g.property.1

/-- 相対入力の quotient 側の全部分圏を与える関手。 -/
def relativeRightFunctor : RelativeStableModel.{u} ⥤ StableModel.{u} where
  obj X := closedStableModel X.right
  map {X Y} f := closedStableMap X.right Y.right f.val f.property.2
  map_id X := closedStableMap_id X.right
  map_comp {X Y Z} f g := closedStableMap_comp X.right Y.right Z.right f.val g.val
    f.property.2 g.property.2

end SerrePositivity.KST.SConstruction
