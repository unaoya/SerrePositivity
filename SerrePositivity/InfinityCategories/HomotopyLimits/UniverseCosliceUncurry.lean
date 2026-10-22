module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCosliceProjection
public import SerrePositivity.InfinityCategories.Core.JoinCurryHomExt
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness

/-!
概要：coslice の元の全錐族の展開は、元の join の宇宙比較と厳密に可換。
方針：各標準単体で元の付随錐を回収し、coslice の宇宙同型の全単体公式を使う。
規約：全錐族と固定図式を保持し、頂点・両端の比較だけで代用しない。
使われ方：持ち上げた局所右 Kan 添字の標準全錐の厳密な同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の join の宇宙同型は、持ち上げた同じ単体の右因子への制限を保つ。 -/
lemma uliftJoinIso_inv_yoneda {K A : SSet.{u}} {n : ℕ} (a : A _⦋n⦌) :
    joinMap (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) (SSet.yonedaEquiv.symm (ULift.up a)) ≫
      (uliftJoinIso.{u, v} K A).inv =
    (uliftCoconeShapeIso.{u, v} K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (joinMap (𝟙 K) (SSet.yonedaEquiv.symm a)) := by
  rw [← uliftYonedaMap a]
  dsimp only [uliftCoconeShapeIso, Iso.trans_inv, joinIso]
  rw [Category.assoc, ← uliftJoinIso_inv_naturality (𝟙 K) (SSet.yonedaEquiv.symm a)]
  simp only [Iso.refl_inv, ← Category.assoc, ← joinMap_comp, Category.id_comp]
  rfl

/-- 元の coslice の全錐族の展開と宇宙持ち上げは、元の全写像として厳密に可換。 -/
lemma sliceUnderUncurry_ulift {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceUnder p) :
    sliceUnderUncurry ((SSet.uliftFunctor.{v, u}).map f ≫ (uliftSliceUnderIso p).hom) =
      (uliftJoinIso.{u, v} K A).inv ≫
        (SSet.uliftFunctor.{v, u}).map (sliceUnderUncurry f) := by
  apply join_right_hom_ext
  · rw [sliceUnderUncurry_fixed]
    have hi : joinInl ((SSet.uliftFunctor.{v, u}).obj K)
        ((SSet.uliftFunctor.{v, u}).obj A) ≫ (uliftJoinIso K A).inv =
        (SSet.uliftFunctor.{v, u}).map (joinInl K A) := by
      apply (cancel_mono (uliftJoinIso K A).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, uliftJoinIso_inl]
    rw [← Category.assoc, hi, ← Functor.map_comp, sliceUnderUncurry_fixed]
  · intro n a
    obtain ⟨⟨a⟩, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
    rw [← sliceUnderUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda]
    change (uliftCoconeShapeIso K n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (f.app _ a).val = _
    rw [← Category.assoc, uliftJoinIso_inv_yoneda, Category.assoc, ← Functor.map_comp]
    have hs : joinMap (𝟙 K) (SSet.yonedaEquiv.symm a) ≫ sliceUnderUncurry f =
        (f.app _ a).val := by
      rw [← sliceUnderUncurry_precomp, SSet.yonedaEquiv_symm_comp, sliceUnderUncurry_yoneda]
    rw [hs]

end SerrePositivity.InfinityCategories.HomotopyLimits
