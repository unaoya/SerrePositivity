module
public import SerrePositivity.InfinityCategories.Core.UniverseSlices

public import SerrePositivity.InfinityCategories.Core.JoinCurryHomExt
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-!
概要：slice の元の全錐族の展開は、元の join の宇宙比較と厳密に可換。
方針：各標準単体で元の付随錐を回収し、slice の宇宙同型の全単体公式を使う。
規約：全錐族と固定図式を保持し、頂点・両端の比較だけで代用しない。
使われ方：持ち上げた局所左 Kan 添字の標準全錐の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の join の宇宙同型は、持ち上げた同じ単体の左因子への制限を保つ。 -/
lemma uliftJoinIso_inv_left_yoneda {K A : SSet.{u}} {n : ℕ} (a : A _⦋n⦌) :
    joinMap (SSet.yonedaEquiv.symm (ULift.up a)) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) ≫
      (uliftJoinIso.{u, v} A K).inv =
    (uliftConeShapeIso.{u, v} K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinMap (SSet.yonedaEquiv.symm a) (𝟙 K)) := by
  rw [← uliftYonedaMap a]
  dsimp only [uliftConeShapeIso, Iso.trans_inv, joinIso]
  rw [Category.assoc, ← uliftJoinIso_inv_naturality (SSet.yonedaEquiv.symm a) (𝟙 K)]
  simp only [Iso.refl_inv, ← Category.assoc, ← joinMap_comp]
  rfl

/-- 元の slice の全錐族の展開と宇宙持ち上げは、元の全写像として厳密に可換。 -/
lemma sliceOverUncurry_ulift {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    sliceOverUncurry ((SSet.uliftFunctor.{v, u}).map f ≫ (uliftSliceOverIso p).hom) =
      (uliftJoinIso.{u, v} A K).inv ≫
        (SSet.uliftFunctor.{v, u}).map (sliceOverUncurry f) := by
  apply join_left_hom_ext
  · rw [sliceOverUncurry_fixed]
    have hi : joinInr ((SSet.uliftFunctor.{v, u}).obj A)
        ((SSet.uliftFunctor.{v, u}).obj K) ≫ (uliftJoinIso A K).inv =
        (SSet.uliftFunctor.{v, u}).map (joinInr A K) := by
      apply (cancel_mono (uliftJoinIso A K).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, uliftJoinIso_inr]
    rw [← Category.assoc, hi, ← Functor.map_comp, sliceOverUncurry_fixed]
  · intro n a
    obtain ⟨⟨a⟩, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
    rw [← sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda]
    change (uliftConeShapeIso K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (f.app _ a).val = _
    rw [← Category.assoc, uliftJoinIso_inv_left_yoneda, Category.assoc, ← Functor.map_comp]
    have hs : joinMap (SSet.yonedaEquiv.symm a) (𝟙 K) ≫ sliceOverUncurry f =
        (f.app _ a).val := by
      rw [← sliceOverUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceOverUncurry_yoneda]
    rw [hs]

end SerrePositivity.InfinityCategories.HomotopyLimits
