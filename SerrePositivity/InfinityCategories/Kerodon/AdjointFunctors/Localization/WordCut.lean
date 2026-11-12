module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
public import Lean.Elab.Tactic.Omega

/-!
# 語の単調写像に沿う頂点の切断位置

概要：列の単調写像から、各終域頂点に対応する始域の切断位置を構成する。
方針：指定頂点より左へ写る列の右端の上限を取り、初期区間の特徴付けを証明。
規約：空 fiber も空語も含む。頂点の作用は列の作用と逆向きになる。
使われ方：同方向列の合成と恒等列の挿入による hammock 図式の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

namespace Hom
variable {a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}

/-- 終域の指定頂点より左へ写る、元の列の初期区間。 -/
def leftColumns (f : a ⟶ b) (j : Fin (b.length + 1)) : Finset (Fin a.length) :=
  Finset.univ.filter (fun i => (f.orderHom i).val < j.val)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (leftColumns)


@[simp] lemma mem_leftColumns (f : a ⟶ b) (j : Fin (b.length + 1)) (i : Fin a.length) :
    i ∈ leftColumns f j ↔ (f.orderHom i).val < j.val := by simp [leftColumns]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (mem_leftColumns)


/-- 初期区間の右端。空区間の右端は零。 -/
def cutNat (f : a ⟶ b) (j : Fin (b.length + 1)) : ℕ :=
  (leftColumns f j).sup (fun i => i.val + 1)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cutNat)


lemma cutNat_le_iff (f : a ⟶ b) (j : Fin (b.length + 1)) (k : ℕ) :
    cutNat f j ≤ k ↔ ∀ i : Fin a.length, (f.orderHom i).val < j.val → i.val < k := by
  simp only [cutNat, Finset.sup_le_iff, mem_leftColumns, Nat.add_one_le_iff]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cutNat_le_iff)


lemma cutNat_le_length (f : a ⟶ b) (j : Fin (b.length + 1)) :
    cutNat f j ≤ a.length :=
  (cutNat_le_iff f j _).2 (fun i _ => i.isLt)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cutNat_le_length)


/-- 各終域頂点に対応する、元の語の実際の頂点。 -/
def cut (f : a ⟶ b) (j : Fin (b.length + 1)) : Fin (a.length + 1) :=
  ⟨cutNat f j, Nat.lt_succ_of_le (cutNat_le_length f j)⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut)


/-- 切断より左の元の列は、ちょうど指定頂点より左へ写る列。 -/
lemma lt_cut_iff (f : a ⟶ b) (j : Fin (b.length + 1)) (i : Fin a.length) :
    i.val < (cut f j).val ↔ (f.orderHom i).val < j.val := by
  constructor
  · intro hi
    by_contra h
    have hb : cutNat f j ≤ i.val := (cutNat_le_iff f j _).2 (by
      intro k hk
      by_contra hki
      have hm := f.orderHom.monotone (show i ≤ k by omega)
      change (f.orderHom i).val ≤ (f.orderHom k).val at hm
      omega)
    change i.val < cutNat f j at hi
    omega
  · intro hi
    have hb := Finset.le_sup (f := fun k : Fin a.length => k.val + 1)
      ((mem_leftColumns f j i).2 hi)
    change i.val < cutNat f j
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hb

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (lt_cut_iff)


/-- 頂点はその左側の全列によって一意に決まる。 -/
lemma vertex_ext {n : ℕ} (p q : Fin (n + 1))
    (h : ∀ i : Fin n, i.val < p.val ↔ i.val < q.val) : p = q := by
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hx := h ⟨p.val, by omega⟩
    simp only at hx
    omega
  · have hx := h ⟨q.val, by omega⟩
    simp only at hx
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (vertex_ext)


@[simp] lemma cut_zero (f : a ⟶ b) : cut f 0 = 0 := by
  apply vertex_ext
  intro i
  rw [lt_cut_iff]
  simp

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut_zero)


@[simp] lemma cut_last (f : a ⟶ b) : cut f (Fin.last b.length) = Fin.last a.length := by
  apply vertex_ext
  intro i
  rw [lt_cut_iff]
  exact iff_of_true (f.orderHom i).isLt i.isLt

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut_last)


/-- 語の恒等射は全頂点の切断位置を固定する。 -/
@[simp] lemma cut_id (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (j : Fin (a.length + 1)) : cut (𝟙 a) j = j := by
  apply vertex_ext
  intro i
  rw [lt_cut_iff]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut_id)


/-- 合成に沿う切断は、二つの元の切断の逆順の合成。 -/
@[simp] lemma cut_comp (f : a ⟶ b) (g : b ⟶ c) (j : Fin (c.length + 1)) :
    cut (f ≫ g) j = cut f (cut g j) := by
  apply vertex_ext
  intro i
  rw [lt_cut_iff, lt_cut_iff, lt_cut_iff]
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut_comp)


/-- 終域の頂点の順序は元の語の切断位置の順序に保たれる。 -/
lemma cut_monotone (f : a ⟶ b) : Monotone (cut f) := by
  intro i j hij
  change cutNat f i ≤ cutNat f j
  apply (cutNat_le_iff f i _).2
  intro k hk
  exact (lt_cut_iff f j k).2 (lt_of_lt_of_le hk hij)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (cut_monotone)


/-- 隣り合う二つの切断の間の列は、ちょうど元の同じ fiber。 -/
lemma fiber_iff (f : a ⟶ b) (j : Fin b.length) (i : Fin a.length) :
    (cut f j.castSucc).val ≤ i.val ∧ i.val < (cut f j.succ).val ↔ f.orderHom i = j := by
  have h₀ := lt_cut_iff f j.castSucc i
  have h₁ := lt_cut_iff f j.succ i
  change i.val < (cut f j.castSucc).val ↔ (f.orderHom i).val < j.val at h₀
  change i.val < (cut f j.succ).val ↔ (f.orderHom i).val < j.val + 1 at h₁
  constructor
  · intro h
    apply Fin.ext
    omega
  · intro h
    have hv := congrArg Fin.val h
    omega

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (fiber_iff)


/-- 合成される一つの fiber の全列は、元の終域の列と同じ向き。 -/
lemma fiber_direction (f : a ⟶ b) (j : Fin b.length) (i : Fin a.length)
    (hi : (cut f j.castSucc).val ≤ i.val) (hi' : i.val < (cut f j.succ).val) :
    a.direction i = b.direction j :=
  (f.direction_eq i).symm.trans (congrArg b.direction ((fiber_iff f j i).1 ⟨hi, hi'⟩))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.Hom export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Hom (fiber_direction)


end Hom
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
