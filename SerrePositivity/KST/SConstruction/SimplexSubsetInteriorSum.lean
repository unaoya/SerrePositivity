module
public import SerrePositivity.KST.SConstruction.SimplexSubsetInteriorCoordinates
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # 元の部分集合の端点で零になる和と内部頂点和
概要：元の所属頂点全体の条件付き和を、元の所属内部頂点の和へ移す。
方針：非零項の元の頂点をそのまま保持する有限和の全単射を使う。
規約：元の端点・所属・依存する寄与を保持。使われ方：HA の右辺の面座標への移送。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.KST.SConstruction
open scoped BigOperators

/-- 元の所属頂点全体の端点で零になる和は、元の所属内部頂点による同じ寄与の和。 -/
lemma simplexSubset_sum_interior {n : ℕ} (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    {M : Type*} [AddCommMonoid M]
    (f : ∀ j ∈ I, I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j →
      j < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) → M) :
    (∑ j : I, if h : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < j.val ∧
        j.val < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) then f j.val j.property h.1 h.2 else 0) =
      ∑ j : SimplexSubsetInterior I hI, f j.val j.property.1 j.property.2.1 j.property.2.2 := by
  classical
  let t (a : I) := if h : I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < a.val ∧
    a.val < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) then f a.val a.property h.1 h.2 else 0
  have hb (a : I) (ha : t a ≠ 0) :
      I.min' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) < a.val ∧
        a.val < I.max' (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexSubsetNonempty I hI) := by
    by_contra h
    exact ha (dite_eq_right h)
  let e (a : I) (ha : t a ≠ 0) : SimplexSubsetInterior I hI :=
    ⟨a.val, a.property, hb a ha⟩
  apply Finset.sum_bij_ne_zero (fun a _ ha => e a ha)
  · intro a _ _
    exact Finset.mem_univ _
  · intro a _ ha b _ hb he
    exact Subtype.ext (congrArg (fun j : SimplexSubsetInterior I hI => j.val) he)
  · intro b _ hb
    let a : I := ⟨b.val, b.property.1⟩
    have ha : t a ≠ 0 := by
      simpa only [a, t, dite_eq_left b.property.2] using hb
    exact ⟨a, Finset.mem_univ _, ha, Subtype.ext rfl⟩
  · intro a _ ha
    exact dite_eq_left (hb a ha)

end SerrePositivity.KST.SConstruction
