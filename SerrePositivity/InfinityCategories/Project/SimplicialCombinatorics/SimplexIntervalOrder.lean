module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # 元の標準単体の有限区間の順序包含
概要：元の二頂点 a≤b の間の全整数頂点を、同じ標準単体へ番号を保って埋め込む。
方針：局所番号に a を加える単調単射を使う。
規約：一点区間も含む。使われ方：necklace augmentation の区間への因数分解。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction
open CategoryTheory _root_.Simplicial SSet

/-- 元の区間 [a,b] の局所番号を、元の標準単体の頂点番号へ戻す順序包含。 -/
def simplexIntervalOrder {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    Fin (b.val - a.val + 1) →o Fin (n + 1) where
  toFun i := ⟨a.val + i.val, by have := b.isLt; have := i.isLt; omega⟩
  monotone' i j h := by
    change a.val + i.val ≤ a.val + j.val
    exact Nat.add_le_add_left h _

/-- 元の区間包含は、元の a に局所番号を加えた番号を回収する。 -/
lemma simplexIntervalOrder_val {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b)
    (i : Fin (b.val - a.val + 1)) : (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab i).val = a.val + i.val := rfl

/-- 元の区間包含は、元の始頂点 a を回収する。 -/
lemma simplexIntervalOrder_first {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab 0 = a := by
  apply Fin.ext
  exact Nat.add_zero _

/-- 元の区間包含は、元の終頂点 b を回収する。 -/
lemma simplexIntervalOrder_last {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab (Fin.last (b.val - a.val)) = b := by
  apply Fin.ext
  change a.val + (b.val - a.val) = b.val
  have h : a.val ≤ b.val := hab
  omega

/-- 元の区間の頂点包含は単射。 -/
lemma simplexIntervalOrder_injective {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change a.val + i.val = a.val + j.val at hv
  omega

/-- 元の区間の順序包含を、元の有限順序の間の単体圏の射として読む。 -/
def simplexIntervalHom {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) :
    ⦋b.val - a.val⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder a b hab)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalHom := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalHom

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder_first := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_first

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder_injective := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_injective

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder_last := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder_val := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder_val

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.SConstruction.simplexIntervalOrder._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexIntervalOrder._proof_3
