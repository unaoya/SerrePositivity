module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StrictAutomorphismShift
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.IsoCat

/-! # 自己同値の skeleton 上の整数シフト

概要：自己同値を skeleton 上の厳密な自己同型に直し、整数シフトを得る。
方針：skeleton 上の充満忠実・対象全単射な関手の厳密な逆を使う。
規約：元の圏を置き換えず、シフトの構成の中間段階だけに skeleton を用いる。
使われ方：S4 の整数シフトの整合性の構成。
-/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：厳密な自己同型を束ねた圏の自己同型群の元にする。
方針：関手と厳密な逆を Cat の同型にまとめる。
規約：単位の等号の向きに注意する。使われ方：整数冪の群構造。 -/
def stableAutOfIsoCat {C : Type u} [Category.{v} C] (e : IsoCat C C) : Aut (Cat.of C) :=
  Aut.of {
    hom := e.functor.toCatHom
    inv := e.inverse.toCatHom
    hom_inv_id := congrArg Functor.toCatHom e.unit_eq.symm
    inv_hom_id := congrArg Functor.toCatHom e.counit_eq }

/-- 概要：自己同値が誘導する skeleton の自己関手は厳密な自己同型になる。
方針：充満忠実性と対象上の全単射性から厳密な逆関手を構成する。
規約：順方向の関手は mapSkeleton そのもの。使われ方：整数シフトの補助モデル。 -/
def stableEquivalenceSkeletonAut {C : Type u} [Category.{v} C] (e : C ≌ C) :
    Aut (Cat.of (Skeleton C)) := by
  let F := e.functor.mapSkeleton
  letI : F.IsIso := {
    bijective_obj := ⟨e.functor.mapSkeleton_injective, e.functor.mapSkeleton_surjective⟩ }
  exact stableAutOfIsoCat F.asIsomorphism

/-- 概要：skeleton 上の厳密な自己同型の順方向は元の自己同値の mapSkeleton。
方針：厳密な逆の構成は順方向を変更しない。
規約：関手の厳密な等号。使われ方：一回シフトの照合。 -/
lemma stableEquivalenceSkeletonAut_functor {C : Type u} [Category.{v} C] (e : C ≌ C) :
    (stableEquivalenceSkeletonAut e).asIso.hom.toFunctor = e.functor.mapSkeleton := rfl

/-- 概要：自己同値からその skeleton 上の整数シフトを得る。
方針：skeleton の厳密な自己同型に整数冪のシフトを適用する。
規約：HasShift の整合条件を全て含む。使われ方：元の圏へのシフトの輸送。 -/
@[instance_reducible]
def stableEquivalenceSkeletonHasShift {C : Type u} [Category.{v} C] (e : C ≌ C) :
    HasShift (Skeleton C) ℤ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutHasShift (stableEquivalenceSkeletonAut e)

/-- 概要：skeleton 上の一回シフトは元の自己同値の mapSkeleton そのもの。
方針：自己同型の一乗を計算する。
規約：局所的に構成したシフト。使われ方：元の Σ と一回シフトの自然同型。 -/
lemma stableEquivalenceSkeletonHasShift_one {C : Type u} [Category.{v} C] (e : C ≌ C) :
    letI := stableEquivalenceSkeletonHasShift e
    shiftFunctor (Skeleton C) (1 : ℤ) = e.functor.mapSkeleton := by
  let := stableEquivalenceSkeletonHasShift e
  change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutPowerFunctor (stableEquivalenceSkeletonAut e) 1 = _
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutPowerFunctor, zpow_one, stableEquivalenceSkeletonAut_functor]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
