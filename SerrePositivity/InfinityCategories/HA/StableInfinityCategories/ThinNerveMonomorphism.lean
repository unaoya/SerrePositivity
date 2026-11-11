module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FinitePosetNerve
public import Mathlib.CategoryTheory.Types.Monomorphisms

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
lemma nerveMap_mono_of_thin_of_obj_injective {I J : Type u} [SmallCategory I]
    [SmallCategory J] [Quiver.IsThin I] (F : I ⥤ J) (hi : Function.Injective F.obj) :
    Mono (nerveMap F) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b h
  apply CategoryTheory.Functor.ext
  · intro i j f
    apply Subsingleton.elim
  · intro i
    apply hi
    exact CategoryTheory.Functor.congr_obj h i

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
