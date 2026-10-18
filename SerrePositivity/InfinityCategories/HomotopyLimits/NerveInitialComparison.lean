module

public import SerrePositivity.InfinityCategories.HomotopyLimits.NerveOpposite
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictCones
public import SerrePositivity.InfinityCategories.Core.JoinCurryHomExt

/-!
概要：同じ始対象または終対象を保つ nerve の単射の anodyne 性。
方針：始対象の錐の自然性から点との join の射への retract を作り、終対象側は反転で移す。
規約：通常の関手 F が指定した始対象・終対象を保ち、nerveMap F が単射であることを明示する。
使われ方：Kerodon 4.7.3.22、7.5.3.12 の over 圏を含む重みの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- 概要：始対象を保つ関手は始対象を前置した射列を保つ。
方針：残りの射列を定義で比較し、先頭からの射は始対象性で一意にする。
規約：始対象の同型ではなく F.obj c 自身の始対象性を仮定する。
使われ方：Kerodon 4.7.3 の始対象の錐の関手に関する自然性。 -/
lemma initialChain_map (F : C ⥤ D) {c : C} (hc : IsInitial c) (hd : IsInitial (F.obj c))
    {n : ℕ} (a : ComposableArrows C n) :
    (F.mapComposableArrows _).obj (initialChain hc a) =
      initialChain hd ((F.mapComposableArrows _).obj a) := by
  refine ComposableArrows.ext_succ ?_ ?_ ?_
  · rfl
  · rfl
  · exact hd.hom_ext _ _
/-- 概要：始対象の錐を任意の標準単体上で射列の前置として表示する。
方針：coslice の uncurry と Yoneda の自然性を用いる。
規約：左因子の点と標準単体の join の同型を明示する。
使われ方：Kerodon 4.7.3 の自然な錐の比較。 -/
lemma nerveInitialCone_simplex {c : C} (hc : IsInitial c) {n : ℕ}
    (a : (Δ[n] : SSet.{u}) ⟶ nerve C) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) a ≫ nerveInitialCone hc =
      (pointJoinStdSimplexIso n).hom ≫
        SSet.yonedaEquiv.symm (initialChain hc (SSet.yonedaEquiv a)) := by
  have hs : a ≫ nerveInitialSection hc =
      SSet.yonedaEquiv.symm (nerveInitialConeSimplex hc (SSet.yonedaEquiv a)) := by
    conv_lhs => rw [← SSet.yonedaEquiv.symm_apply_apply a]
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  rw [nerveInitialCone, ← sliceUnderUncurry_precomp, hs, sliceUnderUncurry_yoneda]
  rfl
/-- 概要：始対象を保つ関手は nerve の始対象からの錐と可換。
方針：頂点と全標準単体で比較し、前置した射列の後合成を計算する。
規約：join からの実際の射の等式。
使われ方：Kerodon 4.7.3.22 の nerve の射の retract。 -/
lemma nerveInitialCone_naturality (F : C ⥤ D) {c : C} (hc : IsInitial c)
    (hd : IsInitial (F.obj c)) :
    nerveInitialCone hc ≫ nerveMap F =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap F) ≫ nerveInitialCone hd := by
  apply join_right_hom_ext
  · rw [← Category.assoc, nerveInitialCone_left]
    rw [← Category.assoc, joinInl_joinMap, Category.id_comp, nerveInitialCone_left]
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp]
    exact nerveMap_app_mk₀ F c
  · intro n a
    rw [← Category.assoc, nerveInitialCone_simplex]
    conv_rhs => rw [← Category.assoc, ← joinMap_comp, Category.id_comp,
      nerveInitialCone_simplex]
    rw [Category.assoc, SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_comp]
    congr 2
    exact initialChain_map F hc hd _
/-- 概要：始対象を保つ nerve の射は、左から点と join した射の retract。
方針：右包含と両側の始対象からの錐を矢の圏の二射にする。
規約：この retract 自体には単射性は不要。
使われ方：Kerodon 4.7.3.22 の共通の始対象による anodyne 判定。 -/
noncomputable def nerveInitialMapRetract (F : C ⥤ D) {c : C}
    (hc : IsInitial c) (hd : IsInitial (F.obj c)) :
    RetractArrow (nerveMap F) (joinMap (𝟙 (Δ[0] : SSet.{u})) (nerveMap F)) where
  i := Arrow.homMk' (joinInr (Δ[0] : SSet.{u}) (nerve C))
    (joinInr (Δ[0] : SSet.{u}) (nerve D)) (by rw [joinInr_joinMap])
  r := Arrow.homMk' (nerveInitialCone hc) (nerveInitialCone hd)
    (nerveInitialCone_naturality F hc hd)
  retract := by
    apply Arrow.hom_ext
    · exact nerveInitialCone_inr hc
    · exact nerveInitialCone_inr hd
/-- 概要：始対象を保つ関手の nerve が単射なら left anodyne。
方針：点との join が単射を left anodyne にする定理を retract で移す。
規約：nerve の単射性と両側の始対象性を省略しない。
使われ方：Kerodon 4.7.3.22 の共通の始対象を持つ圏の包含。 -/
lemma nerveMap_preservingInitial_leftAnodyne (F : C ⥤ D) [Mono (nerveMap F)] {c : C}
    (hc : IsInitial c) (hd : IsInitial (F.obj c)) : leftAnodyneExtensions (nerveMap F) :=
  MorphismProperty.of_retract (nerveInitialMapRetract F hc hd)
    (joinPoint_mono_leftAnodyne (nerveMap F))
/-- 概要：終対象を保つ関手の nerve が単射なら right anodyne。
方針：反転同型で単射性と始対象側の定理を反対圏から移す。
規約：始域と終域に指定した終対象がある。
使われ方：Kerodon 4.7.3.22 の双対、7.5.3.12 の重みの包含。 -/
lemma nerveMap_preservingTerminal_rightAnodyne (F : C ⥤ D) [Mono (nerveMap F)] {c : C}
    (hc : IsTerminal c) (hd : IsTerminal (F.obj c)) : rightAnodyneExtensions (nerveMap F) := by
  apply rightAnodyne_of_op_left
  let e : Arrow.mk (SSet.opFunctor.map (nerveMap F)) ≅ Arrow.mk (nerveMap F.op) :=
    Arrow.isoMk nerveOppositeIso nerveOppositeIso (nerveOppositeMap_naturality F)
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have hmono : (MorphismProperty.monomorphisms SSet.{u})
      (SSet.opFunctor.map (nerveMap F)) := inferInstance
  have : Mono (nerveMap F.op) :=
    ((MorphismProperty.monomorphisms SSet.{u}).arrow_mk_iso_iff e).1 hmono
  exact (leftAnodyneExtensions.arrow_mk_iso_iff e).2
    (nerveMap_preservingInitial_leftAnodyne F.op (hc.op C) (hd.op D))


end SerrePositivity.InfinityCategories.HomotopyLimits
