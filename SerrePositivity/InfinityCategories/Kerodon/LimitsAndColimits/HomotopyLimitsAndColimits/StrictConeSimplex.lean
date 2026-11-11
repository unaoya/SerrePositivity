module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones

/-!
概要：strict な coherent 錐を添字の任意の標準単体で制限した式を計算する。
方針：始対象の nerve 錐を前置した射列で表し、拡大した関手で元の錐の脚へ戻す。
規約：対象・Hom の二宇宙と添字の ULift を明示する。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、逐次図式の再添字の整合性。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

/-- 概要：始対象の nerve 錐を標準単体で制限すると始対象を前置した射列になる。
方針：coslice の uncurry の自然性と標準単体の Yoneda 表示を使う。
規約：n は零を含む任意の次数。
使われ方：Kerodon 7.5.4.6（Tag 03BB）、strict な錐の再添字の計算の準備。 -/
lemma nerveInitialCone_simplex {J : Type u} [SmallCategory J] {j : J}
    (h : IsInitial j) {n : ℕ} (a : (Δ[n] : SSet.{u}) ⟶ nerve J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain h
        (SSet.yonedaEquiv a)) := by
  have hs : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialSection h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialConeSimplex h (SSet.yonedaEquiv a)) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 概要：strict な coherent 錐の任意の単体上の制限は元の射列に錐の脚を前置した表示。
方針：始対象付き添字の単体の式を拡大した関手で写し、元の通常の錐の脚を評価する。
規約：単体 a は元の nerve の ULift を値域とする。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、通常の関手による錐の再添字の厳密な計算。 -/
lemma strictCoherentConeMap_simplex {F : I ⥤ C} (c : Cone F) {n : ℕ}
    (a : (Δ[n] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap c =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋n + 1⦌)
          (ComposableArrows.precomp ((SSet.yonedaEquiv a).down ⋙ F)
            (c.π.app ((SSet.yonedaEquiv a).down.obj 0)))) := by
  let α := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl
  let h := WithInitial.starInitial (C := AsSmall.{v} I)
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c)).app (Opposite.op ⦋n + 1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain h (SSet.yonedaEquiv (a ≫ α))) =
        ComposableArrows.precomp ((SSet.yonedaEquiv a).down ⋙ F)
          (c.π.app ((SSet.yonedaEquiv a).down.obj 0)) := by
    refine ComposableArrows.ext_succ ?_ ?_ ?_
    · rfl
    · rfl
    · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (a ≫ α) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) α ≫ _) = _
      rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) a), ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp]
      simp only [h, Category.assoc]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain h (SSet.yonedaEquiv (a ≫ α))) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C := by
      rw [nerveInitialCone_simplex]
      simp only [Category.assoc]
    _ = _ := by
      rw [← Category.assoc (SSet.yonedaEquiv.symm _),
        SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hs]

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
