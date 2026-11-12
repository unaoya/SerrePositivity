module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial.FullPosetSubsetNerveIso
public import Mathlib.Logic.Equiv.Basic

/-!
概要：固定順序部分の外の点を除去しても、同じ固定部分の nerve を厳密に回収する。
方針：二重部分型を元の固定部分へ潰す順序同型と、元の包含の全射を比較する。
規約：固定部分の点と包含を保持する。
使われ方：下方閉部分を固定する極大点除去帰納の指定余錐の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
variable {P : Type u} [PartialOrder P] (U : Set P) (a : P) (ha : a ∉ U)

/-- 概要：除去後の固定部分を元の固定部分と同定する順序同型。
方針：二重部分型の同値。規約：元の点。使われ方：帰納仮定の固定部分。 -/
def posetSubsetPointRemovalOrderIso :
    {p : {p : P // p ≠ a} // p.val ∈ U} ≃o {p : P // p ∈ U} where
  toEquiv := Equiv.subtypeSubtypeEquivSubtype (fun h hp ↦ ha (hp ▸ h))
  map_rel_iff' := Iff.rfl

/-- 概要：元の固定部分を、点除去部分へ入れる順序包含。
方針：固定部分の外という仮定。規約：元の点。使われ方：二段形状制限。 -/
def posetSubsetPointRemovalLift : {p : P // p ∈ U} →o {p : P // p ≠ a} where
  toFun p := ⟨p.val, fun hp ↦ ha (hp ▸ p.property)⟩
  monotone' := fun _ _ h ↦ h

/-- 概要：点除去後も固定部分の元の包含を回収する。
方針：元の点と射の一致。規約：全射の等号。使われ方：指定全余錐の移送。 -/
lemma posetSubsetPointRemovalLift_comp :
    nerveMap (posetSubsetPointRemovalLift U a ha).toFunctor ≫
      nerveMap (OrderHom.Subtype.val (fun p : P ↦ p ≠ a)).toFunctor =
    nerveMap (OrderHom.Subtype.val U).toFunctor := rfl

/-- 概要：二重部分型からの包含は同じ固定部分の包含へ戻る。
方針：元の点と射の一致。規約：全射の等号。使われ方：帰納仮定の形状照合。 -/
lemma posetSubsetPointRemovalOrderIso_comp :
    nerveMap (posetSubsetPointRemovalOrderIso U a ha).monotone.functor ≫
      nerveMap (posetSubsetPointRemovalLift U a ha).toFunctor =
    nerveMap (OrderHom.Subtype.val (fun p : {p : P // p ≠ a} ↦ p.val ∈ U)).toFunctor := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply CategoryTheory.Functor.ext
  · intro i j f
    exact Subsingleton.elim _ _
  · intro i
    apply Subtype.ext
    rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
