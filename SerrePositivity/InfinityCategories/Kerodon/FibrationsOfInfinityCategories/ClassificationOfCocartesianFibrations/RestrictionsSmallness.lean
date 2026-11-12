module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness

/-!
概要：頂点を覆う二つの部分で値を指定した coherent な写像の小ささ。
方針：一つの写像を基準に取り、指定された制限から全頂点の対象が一致することを示す。
規約：二つの部分は単体全体を覆う必要はなく、頂点だけを覆えばよい。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coslice の固定した底の単体上での小ささ。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：二つの制限で全頂点の値が決まる coherent な写像の型は小さい。
方針：非空の場合は基準の写像と頂点の対象を揃え、固定頂点の写像の型へ単射で入れる。
規約：始域 X は各次数で u に小さい。制限を与える A と B の小ささは不要。
使われ方：Kerodon §5.5.2（Tag 01ZV）、Corollary 5.6.0.6（Tag 028T）、普遍的な pointed-space 射影の小さい fiber。 -/
lemma coherentMap_fixedRestrictions_small
    {D : Type v} [Category.{u} D] [SimplicialCategory D]
    {A B X : SSet.{max u v}} [∀ n, Small.{u} (X.obj n)]
    (j : A ⟶ X) (k : B ⟶ X) (a : A ⟶ SimplicialNerve D) (b : B ⟶ SimplicialNerve D)
    (hcover : ∀ x : X _⦋0⦌,
      (∃ y, j.app (Opposite.op ⦋0⦌) y = x) ∨
        (∃ z, k.app (Opposite.op ⦋0⦌) z = x)) :
    Small.{u} {f : X ⟶ SimplicialNerve D // j ≫ f = a ∧ k ≫ f = b} := by
  classical
  let T := {f : X ⟶ SimplicialNerve D // j ≫ f = a ∧ k ≫ f = b}
  rcases _root_.isEmpty_or_nonempty T with hT | hT
  · let := hT
    infer_instance
  · obtain ⟨f₀⟩ := hT
    let obj : X _⦋0⦌ → D := fun x ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f₀.val.app _ x)
    let code : T → {f : X ⟶ SimplicialNerve D //
        ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (f.app (Opposite.op ⦋0⦌) x) = obj x} := fun f ↦
      ⟨f.val, by
        intro x
        rcases hcover x with ⟨y, rfl⟩ | ⟨z, rfl⟩
        · apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
          exact (congrArg (fun g : A ⟶ SimplicialNerve D ↦ g.app _ y) f.property.1).trans
            (congrArg (fun g : A ⟶ SimplicialNerve D ↦ g.app _ y) f₀.property.1).symm
        · apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
          exact (congrArg (fun g : B ⟶ SimplicialNerve D ↦ g.app _ z) f.property.2).trans
            (congrArg (fun g : B ⟶ SimplicialNerve D ↦ g.app _ z) f₀.property.2).symm⟩
    apply small_of_injective (f := code)
    intro f g h
    apply Subtype.ext
    change (code f).val = (code g).val
    exact congrArg Subtype.val h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
