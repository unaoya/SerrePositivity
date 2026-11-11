module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetSubtypeNerve

/-!
概要：任意の四角形を厳密に保つ比較格子と二段階の局所余極限を構成する。
方針：有限順序添字の厳密左 Kan 拡張と、指定終対象への延長を交互に使う。
規約：各面の押し出し性はまだ結論しない。使われ方：HA 1.4.2.15 の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 元の四角形・局所余極限・指定頂点を厳密に保持する比較。 -/
def posetProductSwapNerveIso (P Q : Type u) [PartialOrder P] [PartialOrder Q] :
    PartOrd.nerveFunctor.obj (PartOrd.of (P × Q)) ≅ nerve Q ⊗ nerve P := by
  letI : SmallCategory (P × Q) := Preorder.smallCategory (P × Q)
  refine
    { hom := ?_
      inv := ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · exact
      { app n := ↾fun s ↦
          ((show Monotone (fun i ↦ (s.obj i).2) from
            fun _ _ h ↦ (s.monotone h).2).functor,
            (show Monotone (fun i ↦ (s.obj i).1) from
              fun _ _ h ↦ (s.monotone h).1).functor)
        naturality := by intros; rfl }
  · exact
      { app n := ↾fun s ↦ (show Monotone (fun i ↦ (s.2.obj i, s.1.obj i)) from
          fun _ _ h ↦ ⟨s.2.monotone h, s.1.monotone h⟩).functor
        naturality := by intros; rfl }
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f
      apply Subsingleton.elim
    · intro i
      rfl
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    apply Prod.ext
    · apply CategoryTheory.Functor.ext
      · intro i j f
        apply Subsingleton.elim
      · intro i
        rfl
    · apply CategoryTheory.Functor.ext
      · intro i j f
        apply Subsingleton.elim
      · intro i
        rfl

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
