module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictCones
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinCurryHomExt

/-!
概要：同じ始対象または終対象を保つ nerve の単射の anodyne 性。
方針：始対象の錐の自然性から点との join の射への retract を作り、終対象側は反転で移す。
規約：通常の関手 F が指定した始対象・終対象を保ち、nerveMap F が単射であることを明示する。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の over 圏を含む重みの比較。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：始対象を保つ関手は始対象を前置した射列を保つ。
方針：残りの射列を定義で比較し、先頭からの射は始対象性で一意にする。
規約：始対象の同型ではなく F.obj c 自身の始対象性を仮定する。
使われ方：Kerodon 4.7.3（Tag 02H6） の始対象の錐の関手に関する自然性。 -/
lemma initialChain_map (F : C ⥤ D) {c : C} (hc : IsInitial c) (hd : IsInitial (F.obj c))
    {n : ℕ} (a : ComposableArrows C n) :
    (F.mapComposableArrows _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain hc a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain hd ((F.mapComposableArrows _).obj a) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · rfl
  · rfl
  · exact hd.hom_ext _ _
/-- 概要：始対象の錐を任意の標準単体上で射列の前置として表示する。
方針：coslice の uncurry と Yoneda の自然性を用いる。
規約：左因子の点と標準単体の join の同型を明示する。
使われ方：Kerodon 4.7.3（Tag 02H6） の自然な錐の比較。 -/
lemma nerveInitialCone_simplex {c : C} (hc : IsInitial c) {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ nerve C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialChain hc (SSet.yonedaEquiv a)) := by
  have hs : a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialSection hc =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialConeSimplex hc (SSet.yonedaEquiv a)) := by
    conv_lhs => rw [← SSet.yonedaEquiv.symm_apply_apply a]
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp, hs, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl
/-- 概要：始対象を保つ関手は nerve の始対象からの錐と可換。
方針：頂点と全標準単体で比較し、前置した射列の後合成を計算する。
規約：join からの実際の射の等式。
使われ方：Kerodon 4.7.3.22（Tag 02J5） の nerve の射の retract。 -/
lemma nerveInitialCone_naturality (F : C ⥤ D) {c : C} (hc : IsInitial c)
    (hd : IsInitial (F.obj c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc ≫ nerveMap F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap F) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hd := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_right_hom_ext
  · rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveInitialCone_left]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.nerveInitialCone_left]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact nerveMap_app_mk₀ F c
  · intro n a
    rw [← Category.assoc, nerveInitialCone_simplex]
    conv_rhs => rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp,
      nerveInitialCone_simplex]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_comp]
    congr 2
    exact initialChain_map F hc hd _
/-- 概要：始対象を保つ nerve の射は、左から点と join した射の retract。
方針：右包含と両側の始対象からの錐を矢の圏の二射にする。
規約：この retract 自体には単射性は不要。
使われ方：Kerodon 4.7.3.22（Tag 02J5） の共通の始対象による anodyne 判定。 -/
noncomputable def nerveInitialMapRetract (F : C ⥤ D) {c : C}
    (hc : IsInitial c) (hd : IsInitial (F.obj c)) :
    RetractArrow (nerveMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap F)) where
  i := Arrow.homMk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve C))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve D)) (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap])
  r := Arrow.homMk' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hc) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone hd)
    (nerveInitialCone_naturality F hc hd)
  retract := by
    apply Arrow.hom_ext
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr hc
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveInitialCone_inr hd
/-- 概要：始対象を保つ関手の nerve が単射なら left anodyne。
方針：点との join が単射を left anodyne にする定理を retract で移す。
規約：nerve の単射性と両側の始対象性を省略しない。
使われ方：Kerodon 4.7.3.22（Tag 02J5） の共通の始対象を持つ圏の包含。 -/
lemma nerveMap_preservingInitial_leftAnodyne (F : C ⥤ D) [Mono (nerveMap F)] {c : C}
    (hc : IsInitial c) (hd : IsInitial (F.obj c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (nerveMap F) :=
  MorphismProperty.of_retract (nerveInitialMapRetract F hc hd)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeAnodyne.joinPoint_mono_leftAnodyne (nerveMap F))
/-- 概要：終対象を保つ関手の nerve が単射なら right anodyne。
方針：反転同型で単射性と始対象側の定理を反対圏から移す。
規約：始域と終域に指定した終対象がある。
使われ方：Kerodon 4.7.3.22（Tag 02J5） の双対、7.5.3.12 の重みの包含。 -/
lemma nerveMap_preservingTerminal_rightAnodyne (F : C ⥤ D) [Mono (nerveMap F)] {c : C}
    (hc : IsTerminal c) (hd : IsTerminal (F.obj c)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (nerveMap F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.rightAnodyne_of_op_left
  let e : Arrow.mk (SSet.opFunctor.map (nerveMap F)) ≅ Arrow.mk (nerveMap F.op) :=
    Arrow.isoMk _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeMap_naturality F)
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have hmono : (MorphismProperty.monomorphisms SSet.{u})
      (SSet.opFunctor.map (nerveMap F)) := inferInstance
  have : Mono (nerveMap F.op) :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff e).1 hmono
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.arrow_mk_iso_iff e).2
    (nerveMap_preservingInitial_leftAnodyne F.op (hc.op C) (hd.op D))


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
