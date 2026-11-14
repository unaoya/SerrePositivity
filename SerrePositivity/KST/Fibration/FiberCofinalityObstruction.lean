module
public import SerrePositivity.KST.Fibration.ConnectiveFiberCriterion
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # 元の接続射が与える cofinality の障害群

中央の指定次数の群が消えるなら、その次数の fiber 群は一つ上の射影の余核。
群同型は K-5 の同じ接続射を誘導し、代表元での作用も厳密に回収する。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 中央の指定次数の群が消えると、同じ実接続射は全射。 -/
lemma fiberBoundary_surjective_of_middleGroup_zero (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (j : ℤ)
    (hz : Subsingleton (NativeFiber.group t 1 0 j)) :
    Function.Surjective (NativeFiber.boundary t ht j) := by
  intro a
  exact (NativeFiber.exact_fiber t ht j a).1 (hz.elim _ _)

/-- 接続射の核は、同じ元の右射影の像そのもの。 -/
lemma fiberBoundary_ker_eq_projection_range (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (j : ℤ) :
    (NativeFiber.boundary t ht j).ker = (NativeFiber.right t (j + 1)).range := by
  ext a
  exact NativeFiber.exact_base t ht j a

/-- 同じ接続射が誘導する、元の射影の余核と fiber 群の同型。 -/
def fiberCofinalityObstructionEquiv (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (j : ℤ)
    (hz : Subsingleton (NativeFiber.group t 1 0 j)) :
    NativeFiber.group t 1 1 (j + 1) ⧸ (NativeFiber.right t (j + 1)).range ≃*
      NativeFiber.group t 0 0 j :=
  (QuotientGroup.quotientMulEquivOfEq
    (fiberBoundary_ker_eq_projection_range t ht j).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (NativeFiber.boundary t ht j)
        (fiberBoundary_surjective_of_middleGroup_zero t ht j hz))

/-- 障害群の同型は、各代表元で元の接続射をそのまま回収する。 -/
theorem fiberCofinalityObstructionEquiv_mk (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (j : ℤ)
    (hz : Subsingleton (NativeFiber.group t 1 0 j)) (a : NativeFiber.group t 1 1 (j + 1)) :
    fiberCofinalityObstructionEquiv t ht j hz (QuotientGroup.mk a) =
      NativeFiber.boundary t ht j a := rfl

/-- 中央項の負一次群が消えると、零次射影の余核が負一次 fiber 群を計算する。 -/
def piZeroCofinalityObstructionEquiv (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (hz : Subsingleton (NativeFiber.group t 1 0 (-1))) :
    NativeFiber.group t 1 1 0 ⧸ (NativeFiber.right t 0).range ≃*
      NativeFiber.group t 0 0 (-1) :=
  fiberCofinalityObstructionEquiv t ht (-1) hz

/-- 零次余核の同型も、代表元では元の負一次接続射そのもの。 -/
theorem piZeroCofinalityObstructionEquiv_mk (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u})
    (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t) (hz : Subsingleton (NativeFiber.group t 1 0 (-1)))
    (a : NativeFiber.group t 1 1 0) :
    piZeroCofinalityObstructionEquiv t ht hz (QuotientGroup.mk a) =
      NativeFiber.boundary t ht (-1) a :=
  fiberCofinalityObstructionEquiv_mk t ht (-1) hz a

end SerrePositivity.KST.Fibration
