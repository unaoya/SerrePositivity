module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeSimplex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeNaturality

/-!
概要：始対象を加える nerve の同型と、始対象の指定錐の構成を照合する。
方針：同じ通常の nerve を標的として、頂点・右境界・混合辺を比較する。
規約：HTT 1.2.8、Kerodon §4.3.5（Tag 017V）の既存構成の法則。
使われ方：離散層条件の指定制限錐と coherent 錐の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 始対象の指定錐の混合辺は、その始対象からの一意な射。 -/
lemma nerveInitialCone_leg {I : Type u} [SmallCategory I] {i : I}
    (hi : IsInitial i) (j : I) :
    (nerveInitialCone hi).app (Opposite.op ⦋1⦌) (coneLegSimplex j) =
      ComposableArrows.mk₁ (hi.to j) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (nerveInitialCone_simplex hi (nervePoint j)) (Opposite.op ⦋1⦌))
    (Join.mkOfSum (n := 1) (l := 1) (r := 1) rfl
      (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)) (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌)))
  simp only [NatTrans.comp_app_apply] at h
  rw [pointJoinStdSimplexIso_zero_leg] at h
  change (nerveInitialCone hi).app _ (coneLegSimplex j) = _ at h
  apply h.trans
  change SSet.yonedaEquiv (X := nerve I) (n := ⦋1⦌)
    ((SSet.yonedaEquiv (X := nerve I) (n := ⦋1⦌)).symm
      (initialChain hi (SSet.yonedaEquiv (nervePoint j)))) = _
  simp only [Equiv.apply_symm_apply, nervePoint]
  refine ComposableArrows.ext₁ rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 始対象付き nerve の同型は、同じ始対象の指定錐を制限したもの。 -/
lemma initialJoinNerveMap_eq_initialCone (I : Type u) [SmallCategory I] :
    initialJoinNerveMap I =
      joinMap (𝟙 Δ[0]) (nerveMap WithInitial.incl) ≫
        nerveInitialCone (WithInitial.starInitial (C := I)) := by
  apply nerve_joinPoint_hom_ext
  · rw [joinInl_initialJoinNerveMap, ← Category.assoc, joinInl_joinMap,
      Category.id_comp, nerveInitialCone_left]
  · rw [joinInr_initialJoinNerveMap, ← Category.assoc, joinInr_joinMap,
      Category.assoc, nerveInitialCone_inr, Category.comp_id]
  · intro i
    rw [NatTrans.comp_app_apply, coneLegSimplex_natural, nerveInitialCone_leg]
    refine ComposableArrows.ext₁ rfl rfl ?_
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 通常の指定錐の nerve は、始対象の標準錐を拡大した関手で送った全錐。 -/
lemma nerveCone_val_initial {I C : Type u} [SmallCategory I] [SmallCategory C]
    {F : I ⥤ C} (c : Cone F) :
    (nerveCone c).val =
      joinMap (𝟙 Δ[0]) (nerveMap WithInitial.incl) ≫
        nerveInitialCone (WithInitial.starInitial (C := I)) ≫
          nerveMap (coneWithInitialFunctor c) := by
  change initialJoinNerveMap I ≫ nerveMap (coneWithInitialFunctor c) = _
  rw [initialJoinNerveMap_eq_initialCone, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
