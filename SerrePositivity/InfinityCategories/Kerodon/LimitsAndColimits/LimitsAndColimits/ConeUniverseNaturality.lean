module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictNerveMaps
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseLimits

/-!
概要：通常の指定錐を AsSmall に移す操作と、nerve の錐の持ち上げを比較する。
方針：既存の点・図式・すべての脚による外延性で、同じ元の錐を照合する。
使われ方：HTT 1.2.8、Kerodon §4.3.5（Tag 017V）の錐の宇宙表示の変更。
規約：指定錐の全射の等式であり、頂点の存在だけへ弱めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {I C : Type u} [SmallCategory I] [SmallCategory C] {F : I ⥤ C}

/-- 元の通常の指定錐を、添字と標的の同じ AsSmall 表示に移す。 -/
def asSmallCone (c : Cone F) :
    Cone ((AsSmall.down : AsSmall.{u + 1} I ⥤ I) ⋙ F ⋙
      (AsSmall.up : C ⥤ AsSmall.{u + 1} C)) :=
  (AsSmall.up.mapCone c).whisker AsSmall.down

/-- 同じ錐の nerve と AsSmall 表示は、全 join 上で可換する。 -/
lemma uliftNerveCone_asSmall_val (c : Cone F) :
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (nerveAsSmallIso.{u, u + 1} I).hom ≫
      (nerveCone (asSmallCone c)).val =
        (nerveCone c).ulift.val ≫ (nerveAsSmallIso.{u, u + 1} C).hom := by
  let j := joinIso (Iso.refl (Δ[0] : SSet.{u + 1})) (nerveAsSmallIso.{u, u + 1} I)
  apply (cancel_epi j.inv).mp
  change j.inv ≫ j.hom ≫ (nerveCone (asSmallCone c)).val =
    j.inv ≫ ((nerveCone c).ulift.val ≫ (nerveAsSmallIso.{u, u + 1} C).hom)
  rw [Iso.inv_hom_id_assoc]
  apply nerve_joinPoint_hom_ext
  · rw [nerveCone_point]
    change nervePoint (AsSmall.up.obj c.pt) =
      joinInl _ _ ≫ (joinMap (𝟙 _) (nerveAsSmallIso.{u, u + 1} I).inv ≫ _)
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp]
    have hv : joinInl (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)) ≫ (nerveCone c).ulift.val =
        SSet.yonedaEquiv.symm (ULift.up (nerveVertex c.pt)) := by
      apply SSet.yonedaEquiv.injective
      rw [Equiv.apply_symm_apply]
      change (nerveCone c).ulift.vertex = _
      rw [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift_vertex,
        nerveCone_vertex]
    rw [← Category.assoc, hv]
    exact (nerveAsSmallIso_vertex C c.pt).symm
  · rw [(nerveCone (asSmallCone c)).property]
    change _ = joinInr _ _ ≫ (joinMap (𝟙 _) (nerveAsSmallIso.{u, u + 1} I).inv ≫ _)
    rw [← Category.assoc, joinInr_joinMap, Category.assoc]
    rw [← Category.assoc (joinInr _ _) (nerveCone c).ulift.val
      (nerveAsSmallIso.{u, u + 1} C).hom, (nerveCone c).ulift.property]
    rfl
  · intro i
    rcases i with ⟨i⟩
    rw [nerveCone_leg]
    change ComposableArrows.mk₁ (AsSmall.up.map (c.π.app i)) =
      ((nerveAsSmallIso.{u, u + 1} C).hom).app _
        (ULift.up ((nerveCone c).val.app _ (coneLegSimplex i)))
    rw [nerveCone_leg]
    change ComposableArrows.mk₁ (AsSmall.up.map (c.π.app i)) =
      ComposableArrows.mk₁ (c.π.app i) ⋙ AsSmall.up
    exact ComposableArrows.ext₁ rfl rfl (by simp)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
