module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ThinNerveMonomorphism
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
概要：有限順序添字の局所余極限から、元の図式に厳密に等しい左 Kan 拡張を得る。
方針：非退化単体の単射性と左 comma の包含で局所添字の有限性を証明する。
規約：元の図式と native な左 Kan 添字を保持する。使われ方：安定性の比較格子。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
lemma finitePosetLeftComma_projection_injective {P Q : Type u} [PartialOrder P]
    [PartialOrder Q] (L : P ⥤ Q) (q : Q) :
    Function.Injective (CostructuredArrow.proj L q).obj := by
  intro a b h
  apply CostructuredArrow.obj_ext a b h
  apply Subsingleton.elim

/-- 同じ有限順序添字の全単体と局所余極限を保持する。 -/
instance finitePosetLeftComma_nerve_finite {P Q : Type u} [PartialOrder P]
    [PartialOrder Q] [Finite P] (L : P ⥤ Q) (q : Q) :
    (nerve (CostructuredArrow L q)).Finite := by
  have : Quiver.IsThin (CostructuredArrow L q) := fun a b ↦
    ⟨fun f g ↦ CostructuredArrow.ext f g (Subsingleton.elim _ _)⟩
  have : Mono (nerveMap (CostructuredArrow.proj L q)) :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nerveMap_mono_of_thin_of_obj_injective (CostructuredArrow.proj L q)
      (finitePosetLeftComma_projection_injective L q)
  exact SSet.finite_of_mono (nerveMap (CostructuredArrow.proj L q))

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
