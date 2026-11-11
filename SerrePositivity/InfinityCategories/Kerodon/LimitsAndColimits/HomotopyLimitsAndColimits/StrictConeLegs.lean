module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones

/-!
概要：strict な錐の coherent 表示の各脚を元の通常の射と同定する。
方針：始対象からの標準錐を頂点に制限し、一次の射列の表示を計算する。
規約：Δ[0]⋆Δ[0] は既存の pointJoinStdSimplexIso で Δ[1] と同定する。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の錐の成分の整合。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：始対象の標準の nerve 錐を任意の対象に制限した脚は始対象からの一意な射。
方針：coslice の普遍性で制限を零単体に戻し、先頭を加えた零射列を計算する。
規約：Δ[0]⋆Δ[0] の正規化を明示する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の strict な錐の脚の計算。 -/
lemma nerveInitialCone_vertexLeg {J : Type u} [SmallCategory J] {j₀ : J}
    (h : IsInitial j₀) (j : J) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h = SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (h.to j)) := by
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialSection h =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialConeSimplex h (ComposableArrows.mk₀ j)) := by
    change (SSet.yonedaEquiv (X := nerve J)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialSection h = _
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).hom ≫ (SSet.yonedaEquiv (X := nerve J)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain h (ComposableArrows.mk₀ j))) = _
  rw [Iso.inv_hom_id_assoc]
  apply congrArg SSet.yonedaEquiv.symm
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [ComposableArrows.mk₁_obj, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
      ComposableArrows.Mk₁.obj, eqToHom_refl, Fin.mk_one, ComposableArrows.mk₁_map,
      ComposableArrows.Mk₁.map, Category.comp_id, Category.id_comp]
    exact h.hom_ext _ _

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]

/-- 概要：始対象を加えた錐の関手は始対象からの一意な射を元の錐の脚へ写す。
方針：WithInitial.lift の混合する射への作用を評価する。
規約：添字は持ち上げた圏の対象。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の通常の錐の成分との一致。 -/
lemma strictConeFunctor_leg {F : I ⥤ C} (c : Cone F) (i : AsSmall.{v} I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c).map (WithInitial.starInitial.to (WithInitial.of i)) =
      c.π.app (AsSmall.down.obj i) := rfl

variable [SimplicialCategory C]

/-- 概要：coherent な錐を添字 i の頂点に制限して得る辺。
方針：右因子の頂点で制限し、二点の join の正規化の逆射を前合成する。
規約：元の添字 i は持ち上げた nerve の頂点として使う。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐 λ̂ の各脚の定義。 -/
noncomputable def strictCoherentConeLeg {F : I ⥤ C} (c : Cone F) (i : I) :
    (Δ[1] : SSet.{max u v}) ⟶ SimplicialNerve C :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₀ i))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentConeMap c

/-- 概要：strict な錐の coherent 表示の各脚は、元の脚の通常の nerve での表示に一致する。
方針：持ち上げた添字の頂点を始対象の錐に代入し、拡大した関手の混合射を評価する。
規約：通常の nerve から coherent nerve への標準射を使った厳密な等式。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.4.6（Tag 03BB） の錐の成分の整合。 -/
lemma strictCoherentConeLeg_eq {F : I ⥤ C} (c : Cone F) (i : I) :
    strictCoherentConeLeg c i = SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ (c.π.app i))) := by
  let p : (Δ[0] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve I) :=
    SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₀ i))
  let α := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl
  let j : WithInitial (AsSmall.{v} I) := WithInitial.of (AsSmall.up.obj i)
  have hpoint : p ≫ α = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j := by
    dsimp only [p, α]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveAsSmallIso_vertex]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    change (nerveMap WithInitial.incl).app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (AsSmall.up.obj i)) = ComposableArrows.mk₀ j
    exact ComposableArrows.ext₀ rfl
  have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) α =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, hpoint]
  let h := WithInitial.starInitial (C := AsSmall.{v} I)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) p ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) α ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h ≫ g) = _
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 Δ[0]) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h ≫ g := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso 0).inv ≫ f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone h ≫ g) hj
    _ = SSet.yonedaEquiv.symm (ComposableArrows.mk₁ (h.to j)) ≫ g := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ g)
        (nerveInitialCone_vertexLeg h j)
    _ = _ := by
      rw [SSet.yonedaEquiv_symm_comp]
      apply congrArg SSet.yonedaEquiv.symm
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent C).app (Opposite.op ⦋1⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor c)).app (Opposite.op ⦋1⦌)
          (ComposableArrows.mk₁ (h.to j))) = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.resizedNerveMap_edge]
      rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
