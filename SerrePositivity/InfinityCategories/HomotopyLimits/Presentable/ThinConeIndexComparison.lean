module

public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.ConeFamilyStrictification
public import SerrePositivity.InfinityCategories.Core.Presentable.ThinNerveExt
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNerveMaps

/-!
概要：thin 圏の同じ錐添字に対する、N の始対象錐と宇宙調整済み join の全単体の比較。
方針：元の全頂点を左右に分け、thin な nerve への射の一意性で全単体へ戻す。
規約：標的の thin 性だけを使い、後合成する Kan 図式に同値性の仮定を置かない。
使われ方：coherent な錐族の実現を N の strictCoherentCone と照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable (I : Type u) [SmallCategory I]

/-- WithInitial と AsSmall の順番を戻す、元の始対象を保つ通常の関手。 -/
def coneIndexResize : WithInitial (AsSmall.{u + 1} I) ⥤ AsSmall.{u + 1} (WithInitial I) :=
  WithInitial.map AsSmall.down ⋙ AsSmall.up

/-- 元の thin 圏の二つの錐添字模型は、全単体で厳密に一致する。 -/
lemma thinConeIndex_comparison [Quiver.IsThin I] :
    joinMap (𝟙 (Δ[0] : SSet.{u + 1}))
        ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
      nerveInitialCone (WithInitial.starInitial (C := AsSmall.{u + 1} I)) ≫
        nerveMap (coneIndexResize I) =
    (uliftInitialConeIso I).inv ≫ (nerveAsSmallIso (WithInitial I)).hom := by
  have : Quiver.IsThin (WithInitial I) := withInitial_isThin I
  have : Quiver.IsThin (AsSmall.{u + 1} (WithInitial I)) := fun x y ↦
    ⟨fun f g ↦ ULift.ext (Subsingleton.elim f.down g.down)⟩
  apply thinNerve_join_hom_ext
  · have hl : joinInl (Δ[0] : SSet.{u + 1})
          ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) ≫
        (joinMap (𝟙 Δ[0]) ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
          nerveInitialCone (WithInitial.starInitial (C := AsSmall.{u + 1} I)) ≫
            nerveMap (coneIndexResize I)) =
      nervePoint (AsSmall.up.obj (WithInitial.star : WithInitial I)) := by
      rw [← Category.assoc, joinInl_joinMap, Category.id_comp, ← Category.assoc,
        nerveInitialCone_left]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp]
      exact nerveMap_app_mk₀ _ _
    rw [hl]
    apply thinNerve_hom_ext
    intro x
    apply ComposableArrows.ext₀
    rfl
  · rw [← Category.assoc, joinInr_joinMap]
    simp only [Category.assoc]
    have hi : joinInr (Δ[0] : SSet.{u + 1})
        (nerve (WithInitial (AsSmall.{u + 1} I))) ≫
        (nerveInitialCone (WithInitial.starInitial (C := AsSmall.{u + 1} I)) ≫
          nerveMap (coneIndexResize I)) = nerveMap (coneIndexResize I) := by
      rw [← Category.assoc, nerveInitialCone_inr, Category.id_comp]
    rw [hi]
    rw [← uliftInitialConeIso_inr I]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact ComposableArrows.ext (fun _ ↦ rfl) (fun _ _ ↦ Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.F2.Presentable
