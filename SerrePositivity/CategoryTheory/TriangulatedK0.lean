module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Ring.NegOnePow

/-! # 三角圏の Grothendieck 群

## 概要

前三角圏の Grothendieck 群 `TriangulatedK0`（対象の類を完全三角形の関係で割ったもの）と、その普遍性 `lift`・`hom_ext`、整数のシフトの類 `[X⟦n⟧] = (-1)^n [X]`（`mk_shift`）を与える。

## 方針

自由アーベル群を完全三角形の関係の生成する部分群で割る。シフトの符号は `X → 0 → X⟦1⟧` の三角形から。

## 規約

Mathlib にはない（提出候補）。

## 使われ方

PerfectComplex の K₀、KTheory、KST、Euler 評価（`Euler`）。
-/

@[expose] public noncomputable section

universe v u v' u' v'' u''

section TriangulatedK0Part

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- 同型関係と完全三角形の加法関係を表す元。 -/
def triangulatedK0Relations : Set (FreeAbelianGroup C) :=
  {a | ∃ X Y : C, Nonempty (X ≅ Y) ∧
    a = FreeAbelianGroup.of X - FreeAbelianGroup.of Y} ∪
  {a | ∃ T : Triangle C, T ∈ distTriang C ∧
    a = FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
      FreeAbelianGroup.of T.obj₃}

/-- 三角圏の対象と完全三角形から定義する Grothendieck 群。 -/
abbrev TriangulatedK0 : Type u :=
  FreeAbelianGroup C ⧸ AddSubgroup.closure (triangulatedK0Relations C)

namespace TriangulatedK0

variable {C}

/-- 対象の Grothendieck 類。 -/
def mk (X : C) : TriangulatedK0 C := QuotientAddGroup.mk (FreeAbelianGroup.of X)

/-- 同型な対象の類は等しい。 -/
lemma mk_iso {X Y : C} (e : X ≅ Y) : mk X = mk Y := by
  unfold mk
  rw [QuotientAddGroup.eq, neg_add_eq_sub, ← neg_sub]
  exact AddSubgroup.neg_mem _
    (AddSubgroup.subset_closure (Or.inl ⟨X, Y, ⟨e⟩, rfl⟩))

/-- 完全三角形の中央の類は両端の類の和である。 -/
lemma mk_triangle (T : Triangle C) (hT : T ∈ distTriang C) :
    mk T.obj₂ = mk T.obj₁ + mk T.obj₃ := by
  unfold mk
  rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq]
  have h₀ : FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ -
      FreeAbelianGroup.of T.obj₃ ∈ AddSubgroup.closure (triangulatedK0Relations C) :=
    AddSubgroup.subset_closure (Or.inr ⟨T, hT, rfl⟩)
  have h := AddSubgroup.neg_mem _ h₀
  convert h using 1
  abel

/-- 同型不変な加法的評価を Grothendieck 群に降ろす。 -/
noncomputable def lift {B : Type*} [AddCommGroup B] (f : C → B)
    (hi : ∀ {X Y : C}, (X ≅ Y) → f X = f Y)
    (ht : ∀ T : Triangle C, T ∈ distTriang C → f T.obj₂ = f T.obj₁ + f T.obj₃) :
    TriangulatedK0 C →+ B :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift f) (by
    rw [AddSubgroup.closure_le]
    rintro a (⟨X, Y, ⟨e⟩, rfl⟩ | ⟨T, hT, rfl⟩)
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, hi e]
    · simp [AddMonoidHom.mem_ker, FreeAbelianGroup.lift_apply_of, ht T hT])

/-- 降ろした評価は各対象上で元の値をとる。 -/
@[simp] lemma lift_mk {B : Type*} [AddCommGroup B] (f : C → B) (hi) (ht) (X : C) :
    lift f hi ht (mk X) = f X := by
  unfold lift mk
  exact (QuotientAddGroup.lift_mk _ _ _).trans (FreeAbelianGroup.lift_apply_of f X)

/-- 準同型の一致は対象の類上で確認すればよい。 -/
@[ext] lemma hom_ext {B : Type*} [AddCommGroup B] {f g : TriangulatedK0 C →+ B}
    (h : ∀ X, f (mk X) = g (mk X)) : f = g := by
  ext X
  exact h X

/-- 零対象の類は零である。 -/
@[simp] lemma mk_zero : mk (0 : C) = 0 := by
  have h := mk_triangle (contractibleTriangle (0 : C)) (contractible_distinguished _)
  simpa using (add_left_cancel (a := mk (0 : C)) (by simpa using h.symm))

/-- 任意の零対象の類は零である。 -/
lemma mk_of_isZero (X : C) (hX : IsZero X) : mk X = 0 := by
  rw [mk_iso (hX.iso (isZero_zero C)), mk_zero]

/-- 一回のシフトは Grothendieck 類の符号を変える。 -/
lemma mk_shift_one (X : C) : mk (X⟦(1 : ℤ)⟧) = -mk X := by
  have h := mk_triangle _ (contractible_distinguished₂ X)
  change mk (0 : C) = mk X + mk (X⟦(1 : ℤ)⟧) at h
  rw [mk_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

/-- 三角関手が誘導する Grothendieck 群の準同型。 -/
noncomputable def map : TriangulatedK0 C →+ TriangulatedK0 D :=
  lift (fun X ↦ mk (F.obj X)) (fun e ↦ mk_iso (F.mapIso e))
    (fun T hT ↦ mk_triangle _ (F.map_distinguished T hT))

/-- 誘導写像は対象の類を像の類に移す。 -/
@[simp] lemma map_mk (X : C) : map F (mk X) = mk (F.obj X) := lift_mk ..

/-- 恒等関手の誘導写像は恒等準同型である。 -/
@[simp] lemma map_id : map (𝟭 C) = AddMonoidHom.id (TriangulatedK0 C) := by
  apply hom_ext
  intro X
  simp

variable {E : Type u''} [Category.{v''} E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  (G : D ⥤ E) [G.CommShift ℤ] [G.IsTriangulated]

/-- 三角関手の合成と誘導写像の合成は一致する。 -/
@[simp] lemma map_comp : map (F ⋙ G) = (map G).comp (map F) := by
  apply hom_ext
  intro X
  simp

/-- 自然同型な三角関手は同じ誘導写像を与える。 -/
lemma map_natIso {F' : C ⥤ D} [F'.CommShift ℤ] [F'.IsTriangulated] (e : F ≅ F') :
    map F = map F' := by
  apply hom_ext
  intro X
  simpa using mk_iso (e.app X)

end TriangulatedK0

end SerrePositivity

end TriangulatedK0Part

section TriangulatedK0ShiftPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
namespace TriangulatedK0
variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
/-- Integer shifts multiply Grothendieck classes by the corresponding sign. -/
lemma mk_shift (X : C) (n : ℤ) : mk (X⟦n⟧) = ((n.negOnePow : ℤˣ) : ℤ) • mk X := by
  induction n using Int.induction_on with
  | zero =>
    rw [Int.negOnePow_zero, Units.val_one, one_smul]
    exact mk_iso ((shiftFunctorZero C ℤ).app X)
  | succ n ih =>
    have h := mk_iso ((shiftFunctorAdd' C (n : ℤ) 1 (n + 1) rfl).app X)
    simp only [Functor.comp_obj] at h
    rw [h, mk_shift_one, ih, Int.negOnePow_succ, Units.val_neg, neg_smul]
  | pred n ih =>
    have h := mk_iso ((shiftFunctorAdd' C (-n - 1 : ℤ) 1 (-n) (by omega)).app X)
    simp only [Functor.comp_obj] at h
    rw [mk_shift_one, ih] at h
    rw [← neg_neg (mk (X⟦(-n - 1 : ℤ)⟧)), ← h, Int.negOnePow_sub,
      Int.negOnePow_one, mul_neg, mul_one, Units.val_neg, neg_smul]
end TriangulatedK0
end SerrePositivity

end TriangulatedK0ShiftPart
