module

public import SerrePositivity.InfinityCategories.Stable.SliceOpposite
public import SerrePositivity.InfinityCategories.Core.SliceMap

/-!
概要：slice の反転同型は普遍錐の展開を join の反転に移す。
方針：各標準単体の反転と Yoneda 射を比較し、slice の curry の往復を使う。
規約：固定図式とパラメータは任意の単体集合。
使われ方：左 Kan の局所比較の指定変換が反転で保存されることの確認。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：slice の図式を反転すると、join の反転で得る coslice の図式になる。
方針：標準単体の反転同型と Yoneda 射を交換し、join の逆反転の自然性を使う。
規約：普遍錐の固定条件は元の図式の固定条件から計算する。
使われ方：反転後の coslice の普遍錐の同定。 -/
lemma kanSliceOverOpIso_curry {A K X : SSet.{u}} {p : K ⟶ X} (f : A ⟶ sliceOver p) :
    SSet.opFunctor.map f ≫ (sliceOverOpIso p).hom =
      sliceUnderCurry ((stableJoinReverseIso A K).inv ≫ SSet.opFunctor.map (sliceOverUncurry f))
        (by rw [← Category.assoc, stableJoinReverse_inl_inv,
          ← CategoryTheory.Functor.map_comp, sliceOverUncurry_fixed]) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  have hy : SSet.yonedaEquiv.symm a = (stdSimplex.opIso ⦋n⦌).inv ≫
      SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv a)) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply, stableReverseSimplex_yoneda,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have hn := stableJoinReverse_inv_naturality
    (SSet.yonedaEquiv.symm (SSet.opObjEquiv a)) (𝟙 K)
  simp only [CategoryTheory.Functor.map_id] at hn
  have hh := congrArg Subtype.val (ConcreteCategory.congr_hom
    (NatTrans.congr_app (sliceOverCurry_uncurry f) (Opposite.op ⦋n⦌)) (SSet.opObjEquiv a))
  change joinMap (SSet.yonedaEquiv.symm (SSet.opObjEquiv a)) (𝟙 K) ≫
    sliceOverUncurry f = (f.app (Opposite.op ⦋n⦌) (SSet.opObjEquiv a)).val at hh
  change (sliceOverOpObjEquiv p ⦋n⦌ ((SSet.opFunctor.map f).app (Opposite.op ⦋n⦌) a)).val =
    joinMap (𝟙 K.op) (SSet.yonedaEquiv.symm a) ≫
      (stableJoinReverseIso A K).inv ≫ SSet.opFunctor.map (sliceOverUncurry f)
  rw [sliceOverOpObjEquiv_val, hy]
  have hj := joinMap_comp (𝟙 K.op) (𝟙 K.op) (stdSimplex.opIso ⦋n⦌).inv
    (SSet.opFunctor.map (SSet.yonedaEquiv.symm (SSet.opObjEquiv a)))
  simp only [Category.id_comp] at hj
  erw [hj, Category.assoc, reassoc_of% hn, ← CategoryTheory.Functor.map_comp, hh]
  rfl

/-- 概要：反転した slice の普遍錐の展開は元の普遍錐の反転。
方針：反転の curry 表示と coslice の curry・uncurry の往復。
規約：quasicategory 性は不要。
使われ方：局所指定変換の反転の計算。 -/
lemma kanSliceOverOpIso_uncurry {A K X : SSet.{u}} {p : K ⟶ X}
    (f : A ⟶ sliceOver p) :
    sliceUnderUncurry (SSet.opFunctor.map f ≫ (sliceOverOpIso p).hom) =
      (stableJoinReverseIso A K).inv ≫ SSet.opFunctor.map (sliceOverUncurry f) := by
  rw [kanSliceOverOpIso_curry, sliceUnderUncurry_curry]

end SerrePositivity.InfinityCategories.F1B
