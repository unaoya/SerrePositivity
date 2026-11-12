module
public import SerrePositivity.KST.Fibration.ConnectiveFiberObstruction

/-! # 連結 fiber に対する零次 cofinality 条件の必要十分性

K-5 の元の整数長完全列だけを使う。中央項と右項の連結性の下では、
実 fiber が連結であることと、元の右射影が零次で全射であることが同値。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 中央の群が自明なら、左群の消滅は同じ接続射の自明性から従う。 -/
lemma fiberGroup_zero_of_boundary_trivial (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ)
    (hz : Subsingleton (NativeFiber.group t 1 0 j))
    (hb : ∀ a, NativeFiber.boundary t ht j a = 1) :
    Subsingleton (NativeFiber.group t 0 0 j) := by
  have h : ∀ a : NativeFiber.group t 0 0 j, a = 1 := by
    intro a
    obtain ⟨b, hba⟩ := (NativeFiber.exact_fiber t ht j a).1 (hz.elim _ _)
    exact hba.symm.trans (hb b)
  exact ⟨fun a b => (h a).trans (h b).symm⟩

/-- 中央・右群の同じ下界の下で、fiber の下界と端の射影の全射性を同定する。 -/
theorem fiberGroup_lowerBound_iff_projection_surjective (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (k : ℤ)
    (hmid : ∀ j : ℤ, j < k → Subsingleton (NativeFiber.group t 1 0 j))
    (hbase : ∀ j : ℤ, j < k → Subsingleton (NativeFiber.group t 1 1 j)) :
    (∀ j : ℤ, j < k → Subsingleton (NativeFiber.group t 0 0 j)) ↔
      Function.Surjective (NativeFiber.right t k) := by
  constructor
  · intro h
    have hs := fiberProjection_surjective_of_fiberGroup_zero t ht (k - 1)
      (h (k - 1) (by omega))
    have hk : k - 1 + 1 = k := by omega
    rw [hk] at hs
    exact hs
  · intro hs j hj
    apply fiberGroup_zero_of_boundary_trivial t ht j (hmid j hj)
    by_cases he : j + 1 = k
    · apply (fiberProjection_surjective_iff_boundary_trivial t ht j).1
      rw [he]
      exact hs
    · intro a
      have hz := hbase (j + 1) (by omega)
      rw [hz.elim a 1, map_one]

/-- 連結な中央項・右項を持つ実 fiber の連結性は、零次 cofinality と同値。 -/
theorem connectiveFiber_iff_projection_piZero_surjective (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t)
    (hmid : ∀ j : ℤ, j < 0 → Subsingleton (NativeFiber.group t 1 0 j))
    (hbase : ∀ j : ℤ, j < 0 → Subsingleton (NativeFiber.group t 1 1 j)) :
    (∀ j : ℤ, j < 0 → Subsingleton (NativeFiber.group t 0 0 j)) ↔
      Function.Surjective (NativeFiber.right t 0) :=
  fiberGroup_lowerBound_iff_projection_surjective t ht 0 hmid hbase

end SerrePositivity.KST.Fibration
