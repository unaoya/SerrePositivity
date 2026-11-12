module
public import SerrePositivity.KST.SConstruction.NecklaceWedgeBeadOneFace
public import Mathlib.Order.Hom.Set

/-! # 元の一 bead の右端座標の頂点番号
概要：元の一 bead の右端からの cube 座標と、元の局所頂点番号の和を同定する。
方針：元の昇順列挙の像と厳密単調性の一意性から番号を回収する。
規約：座標零は元の右端内部頂点。使われ方：HA の右側頂点数による符号との比較。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open CategoryTheory

/-- 元の一 bead の昇順非 joint 列挙は、元の局所番号に一を加えた頂点。 -/
lemma necklaceSingleAscending_val (N : ℕ) (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending i).val.val = i.val + 1 := by
  let f : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension → ℕ :=
    fun w => ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).val.val
  let g : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension → ℕ := fun w => w.val + 1
  have hd : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension = N - 1 := necklaceBead_dimension.{0} N
  have hf : StrictMono f := fun _ _ h => (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending.strictMono h
  have hg : StrictMono g := by intro a b h; exact Nat.add_lt_add_right h 1
  have hr : Set.range f = {k | 0 < k ∧ k < N} := by
    ext k
    constructor
    · rintro ⟨w, rfl⟩
      have hv := ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).property
      have hb : ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).val.val < N + 1 :=
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).val.isLt
      change _ ∉ ({0, N} : Finset ℕ) at hv
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      change 0 < ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).val.val ∧
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending w).val.val < N
      constructor <;> omega
    · rintro ⟨hk, hN⟩
      let v : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).NonjointVertex := ⟨⟨k, by change k < N + 1; omega⟩, by
        change k ∉ ({0, N} : Finset ℕ)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        omega⟩
      refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending.symm v, ?_⟩
      exact congrArg (fun w : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).NonjointVertex => w.val.val)
        ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending.apply_symm_apply v)
  have hs : Set.range g = {k | 0 < k ∧ k < N} := by
    ext k
    constructor
    · rintro ⟨w, rfl⟩
      have hw := w.isLt
      change 0 < w.val + 1 ∧ w.val + 1 < N
      constructor <;> omega
    · rintro ⟨hk, hN⟩
      refine ⟨⟨k - 1, by omega⟩, ?_⟩
      change k - 1 + 1 = k
      omega
  exact congrFun (hf.eq_of_range_eq hg (hr.trans hs.symm)) i

/-- 元の一 bead の非 joint 頂点番号と右端からの座標に一を加えると、元の最終番号。 -/
lemma necklaceSingleCoordinate_val (N : ℕ) (i : Fin (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension) :
    ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointCoordinate i).val.val + i.val + 1 = N := by
  have ha := necklaceSingleAscending_val N i.rev
  have hd : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).dimension = N - 1 := necklaceBead_dimension.{0} N
  have hi := i.isLt
  change ((_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.NecklaceShape.single N).nonjointAscending i.rev).val.val + i.val + 1 = N
  have hr := Fin.val_rev i
  omega

end SerrePositivity.KST.SConstruction
