module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KappaFilteredUniverse

/-!
概要：元の poset の nerve と反対 nerve を、宇宙を持ち上げた同じ poset の nerve と同定する。
方針：順序同型の対象・射への作用と、反対圏から順序双対への通常の同型を使う。
規約：元の対象を保持し、反対圏と順序双対を定義的に同一視しない。
使われ方：N の大きい Hom 錐の反対形状を、実証済みの poset 極限交換へ渡す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の poset の nerve の持ち上げは、持ち上げた同じ順序の nerve と厳密に同型。 -/
def nervePosetUniverseIso (I : Type u) [Preorder I] :
    (SSet.uliftFunctor.{v, u}).obj (nerve I) ≅ nerve (ULift.{v} I) where
  hom := {
    app _ := ↾fun s ↦ s.down ⋙
      (⟨ULift.up, fun _ _ h ↦ h⟩ : I →o ULift.{v} I).toFunctor
    naturality _ _ _ := rfl }
  inv := {
    app _ := ↾fun s ↦ ULift.up (s ⋙
      (⟨ULift.down, fun _ _ h ↦ h⟩ : ULift.{v} I →o I).toFunctor)
    naturality _ _ _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

/-- poset の反対圏から元の順序双対への、元の対象を保つ関手。 -/
def posetOppositeToDual (I : Type u) [Preorder I] : Iᵒᵖ ⥤ OrderDual I where
  obj i := i.unop
  map f := homOfLE (leOfHom f.unop)

/-- 順序双対から元の poset の反対圏への逆関手。 -/
def posetDualToOpposite (I : Type u) [Preorder I] : OrderDual I ⥤ Iᵒᵖ where
  obj i := Opposite.op i
  map f := (homOfLE (leOfHom f)).op

/-- 反対 nerve を元の順序双対の nerve に戻す、全単体の同型。 -/
def nervePosetOppositeIso (I : Type u) [Preorder I] : (nerve I).op ≅ nerve (OrderDual I) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso ≪≫ {
    hom := nerveMap (posetOppositeToDual I)
    inv := nerveMap (posetDualToOpposite I)
    hom_inv_id := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)
    inv_hom_id := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _) }

/-- 宇宙を持ち上げた反対形状も、同じ持ち上げた順序双対の nerve と同型。 -/
def nervePosetUniverseOppositeIso (I : Type u) [Preorder I] :
    ((SSet.uliftFunctor.{v, u}).obj (nerve I)).op ≅ nerve (ULift.{v} (OrderDual I)) :=
  (show ((SSet.uliftFunctor.{v, u}).obj (nerve I)).op ≅
      (SSet.uliftFunctor.{v, u}).obj ((nerve I).op) from Iso.refl _) ≪≫
    (SSet.uliftFunctor.{v, u}).mapIso (nervePosetOppositeIso I) ≪≫
      nervePosetUniverseIso (OrderDual I)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
