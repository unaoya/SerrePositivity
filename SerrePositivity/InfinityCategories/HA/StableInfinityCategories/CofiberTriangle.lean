module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Shift
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberConnectingVanishing
public import Mathlib.CategoryTheory.Triangulated.Basic

/-! # 通常の三角形としての cofiber 列

概要：cofiber 列を Mathlib の Triangle に送り、実際のホモトピーから三角形の射を得る。
方針：接続射を一回シフトと Σ の比較同型で送り、自然性で第三の可換式を証明する。
規約：distinguished の公理と前加法構造はまだ仮定・主張しない。
使われ方：S4 の三角構造の基礎となる三角形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：安定 ∞ 圏の cofiber 列からホモトピー圏の通常の三角形を得る。
方針：最初の二射は短複体から取り、接続射を Σ から一回シフトへ移す。
規約：Mathlib の Triangle を使う。使われ方：distinguished triangle の代表。 -/
def cofiberTriangle {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) : Pretriangulated.Triangle (hoFunctor.obj X) :=
  Pretriangulated.Triangle.mk t.hoShortComplex.f t.hoShortComplex.g
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app t.hoShortComplex.X₁)

/-- 概要：cofiber 三角形の最初の二射の合成は零。
方針：短複体の零合成を使う。規約：構成した三角形。
使われ方：三角形の隣接零合成。 -/
lemma cofiberTriangle_mor₁_comp_mor₂ {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (cofiberTriangle t ht).mor₁ ≫ (cofiberTriangle t ht).mor₂ = 0 := t.hoShortComplex.zero

/-- 概要：cofiber 三角形の第二射と第三射の合成は零。
方針：Σ への接続射の零合成を一回シフトに移す。
規約：構成した三角形。使われ方：三角形の隣接零合成。 -/
lemma cofiberTriangle_mor₂_comp_mor₃ {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (cofiberTriangle t ht).mor₂ ≫ (cofiberTriangle t ht).mor₃ = 0 := by
  change t.hoShortComplex.g ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ _) = 0
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_comp_eq_zero, zero_comp (C := hoFunctor.obj X)]

/-- 概要：cofiber 三角形の第三射と最初の射の一回シフトの合成は零。
方針：一回シフトと Σ の自然同型の自然性で既存の零合成へ移す。
規約：構成した整数シフト。使われ方：三角形の三つ目の隣接零合成。 -/
lemma cofiberTriangle_mor₃_comp_shift_mor₁ {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    (cofiberTriangle t ht).mor₃ ≫ (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map
      (cofiberTriangle t ht).mor₁ = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app _) ≫
    (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map t.hoShortComplex.f = 0
  rw [Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.naturality,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_comp_suspension_map_eq_zero,
    zero_comp (C := hoFunctor.obj X)]

/-- 概要：cofiber 四角形間の実際のホモトピーは通常の三角形の射を与える。
方針：短複体の比較の三成分を使い、接続射とシフト比較の自然性で第三の可換式を示す。
規約：任意の h の可換正方形からの延長は別途必要。
使われ方：cofiber 三角形の比較と TR3 の基礎。 -/
def cofiberTriangleMapOfHomotopy {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (t d : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) (hd : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence d)
    (H : SSet.Homotopy t.square d.square) : cofiberTriangle t ht ⟶ cofiberTriangle d hd := by
  let m := t.hoShortComplexMapOfHomotopy d H.h H.h₀ H.h₁
  refine {
    hom₁ := m.τ₁
    hom₂ := m.τ₂
    hom₃ := m.τ₃
    comm₁ := m.comm₁₂.symm
    comm₂ := m.comm₂₃.symm
    comm₃ := ?_ }
  change (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app _) ≫
    (shiftFunctor (hoFunctor.obj X) (1 : ℤ)).map m.τ₁ =
      m.τ₃ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.app _)
  rw [Category.assoc, ← (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.shiftOneSuspensionIso X).inv.naturality, ← Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting_naturality_of_homotopy t d ht hd H
  change m.τ₃ ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting d hd =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberConnecting t ht ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor X).map m.τ₁ at h
  rw [← h, Category.assoc]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
