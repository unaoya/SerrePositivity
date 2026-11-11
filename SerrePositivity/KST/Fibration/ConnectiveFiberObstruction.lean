module
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-! # 連結版 fiber 列の零次の必要条件

実 Sp fiber 四角形の長完全列から、射影の全射性の障害を接続射で表す。
左項が連結なら零次射影は全射でなければならない。冪等完備化された商への
比較でこの条件を省略しないための検査であり、fibration 定理自体は仮定しない。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 右射影の全射性は、その次の実接続射の自明性と同値。 -/
lemma fiberProjection_surjective_iff_boundary_trivial (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) :
    Function.Surjective (NativeFiber.right t (j + 1)) ↔
      ∀ a, NativeFiber.boundary t ht j a = 1 := by
  constructor
  · intro h a
    exact (NativeFiber.exact_base t ht j a).2 (h a)
  · intro h a
    exact (NativeFiber.exact_base t ht j a).1 (h a)

/-- 左項の指定次数の消滅は、その次の射影の全射性を与える。 -/
lemma fiberProjection_surjective_of_fiberGroup_zero (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t) (j : ℤ) (hz : Subsingleton (NativeFiber.group t 0 0 j)) :
    Function.Surjective (NativeFiber.right t (j + 1)) :=
  (fiberProjection_surjective_iff_boundary_trivial t ht j).2 (fun _ => hz.elim _ _)

/-- 連結な左項を持つ実 fiber 列は、元の零次射影が全射であることを強制する。 -/
theorem connectiveFiber_projection_piZero_surjective (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsFiberSequence t)
    (hconn : ∀ j : ℤ, j < 0 → Subsingleton (NativeFiber.group t 0 0 j)) :
    Function.Surjective (NativeFiber.right t 0) := by
  simpa only [Int.reduceNeg, Int.reduceAdd] using
    fiberProjection_surjective_of_fiberGroup_zero t ht (-1) (hconn (-1) (by decide))

end SerrePositivity.KST.Fibration
