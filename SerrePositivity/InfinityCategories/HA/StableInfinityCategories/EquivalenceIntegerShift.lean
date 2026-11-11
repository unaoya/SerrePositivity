module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceSkeletonShift
public import Mathlib.CategoryTheory.Shift.Induced

/-! # 自己同値からの整数シフト

概要：任意の自己同値から元の圏の整合的な整数シフトを作る。
方針：skeleton 上の整数冪のシフトを圏同値に沿って誘導する。
規約：一回シフトと元の自己同値の自然同型を公開する。
使われ方：S4 の h C の整数シフトと cofiber 三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe v u
open CategoryTheory Functor
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：skeleton 上の整数冪の自己関手を元の圏へ運ぶ。
方針：skeleton との圏同値の逆・順方向の関手で挟む。
規約：この段階では関手の族。使われ方：誘導シフトの関手。 -/
def stableEquivalenceShiftFamily {C : Type u} [Category.{v} C] (e : C ≌ C) (n : ℤ) : C ⥤ C :=
  (skeletonEquivalence C).inverse ⋙
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutPowerFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonAut e) n ⋙ (skeletonEquivalence C).functor

/-- 概要：skeleton との圏同値は整数冪の関手の族と自然同型を介して可換。
方針：skeleton との圏同値の単位を一度消す。
規約：誘導シフトの構成に必要な全整数の比較。使われ方：HasShift.induced の入力。 -/
def stableEquivalenceShiftFamilyComparison {C : Type u} [Category.{v} C] (e : C ≌ C) (n : ℤ) :
    letI := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonHasShift e
    (skeletonEquivalence C).functor ⋙ stableEquivalenceShiftFamily e n ≅
      shiftFunctor (Skeleton C) n ⋙ (skeletonEquivalence C).functor := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonHasShift e
  let E := skeletonEquivalence C
  exact (Functor.associator E.functor E.inverse
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutPowerFunctor (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonAut e) n ⋙ E.functor)).symm ≪≫
    isoWhiskerRight E.unitIso.symm _ ≪≫ Functor.leftUnitor _

/-- 概要：自己同値から元の圏に整数シフトを構成する。
方針：skeleton のシフトを充満忠実な圏同値に沿って誘導し、全整合条件を転送する。
規約：元の圏の対象・射は変えない。使われ方：h C の整数シフト。 -/
@[instance_reducible]
def stableEquivalenceHasShift {C : Type u} [Category.{v} C] (e : C ≌ C) : HasShift C ℤ := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonHasShift e
  exact HasShift.induced (skeletonEquivalence C).functor ℤ (stableEquivalenceShiftFamily e)
    (stableEquivalenceShiftFamilyComparison e)

/-- 概要：構成した整数シフトの関手は指定した関手の族そのもの。
方針：誘導シフトの定義を計算する。
規約：厳密な関手の等式。使われ方：一回シフトの照合。 -/
lemma stableEquivalenceHasShift_shiftFunctor {C : Type u} [Category.{v} C] (e : C ≌ C) (n : ℤ) :
    letI := stableEquivalenceHasShift e
    shiftFunctor C n = stableEquivalenceShiftFamily e n := rfl

/-- 概要：構成した一回シフトは元の自己同値の順方向の関手と自然同型。
方針：skeleton 上の一乗を元の関手に戻し、圏同値の余単位を二回消す。
規約：シフトの単位・結合の整合性を保った上での比較。
使われ方：接続射を X⟦1⟧ に値を持つ射にする。 -/
def stableEquivalenceShiftOneIso {C : Type u} [Category.{v} C] (e : C ≌ C) :
    letI := stableEquivalenceHasShift e
    shiftFunctor C (1 : ℤ) ≅ e.functor := by
  letI := stableEquivalenceHasShift e
  change stableEquivalenceShiftFamily e 1 ≅ e.functor
  dsimp only [stableEquivalenceShiftFamily, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableAutPowerFunctor]
  rw [zpow_one, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEquivalenceSkeletonAut_functor]
  let E := skeletonEquivalence C
  change (E.inverse ⋙ E.functor ⋙ e.functor) ⋙ (E.inverse ⋙ E.functor) ≅ e.functor
  exact isoWhiskerLeft (E.inverse ⋙ E.functor ⋙ e.functor) E.counitIso ≪≫
    Functor.rightUnitor _ ≪≫ isoWhiskerRight E.counitIso e.functor ≪≫ Functor.leftUnitor _

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
