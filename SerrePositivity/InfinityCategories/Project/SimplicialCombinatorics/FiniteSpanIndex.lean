module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.DeriveFintype

/-!
概要：標準 span を表す三点の有限半順序集合と、その頂点符号を定義する。
方針：一つの始点の上に比較不能な二点を置く。
規約：ULift により任意の小さい宇宙に同じ三点を置く。
使われ方：標準 span/cospan の nerve 表示と Ind の有限半順序結果の宇宙接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 標準 span の三つの頂点。 -/
inductive FiniteSpanVertex | zero | left | right deriving DecidableEq, Fintype

instance : PartialOrder FiniteSpanVertex where
  le x y := x = .zero ∨ x = y
  le_refl _ := Or.inr rfl
  le_trans _ _ _ h k := by
    rcases h with h | rfl
    · exact Or.inl h
    · exact k
  le_antisymm x y h k := by
    rcases h with rfl | h
    · rcases k with rfl | k
      · rfl
      · exact k.symm
    · exact h

/-- 任意の小さい宇宙に置いた標準 span の添字。 -/
abbrev FiniteSpanIndex := ULift.{u} FiniteSpanVertex

/-- 三点の標準番号。 -/
def finiteSpanVertexCode : FiniteSpanVertex → Fin 3
  | .zero => 0 | .left => 1 | .right => 2

/-- 標準単体への単調な符号化。 -/
def finiteSpanCode : FiniteSpanIndex.{u} →o Fin 3 where
  toFun x := finiteSpanVertexCode x.down
  monotone' := by
    intro x y h
    change x.down = .zero ∨ x.down = y.down at h
    change finiteSpanVertexCode x.down ≤ finiteSpanVertexCode y.down
    rcases h with h | h
    · rw [h]
      exact Fin.zero_le _
    · rw [h]

/-- 標準番号を同じ三点へ戻す。 -/
def finiteSpanDecode (i : Fin 3) : FiniteSpanIndex.{u} :=
  ULift.up (if i = 0 then .zero else if i = 1 then .left else .right)

/-- 符号と復号の順方向の往復。 -/
lemma finiteSpanCode_decode (i : Fin 3) : finiteSpanCode (finiteSpanDecode i) = i := by
  fin_cases i <;> decide

/-- 符号と復号の逆方向の往復。 -/
lemma finiteSpanDecode_code (x : FiniteSpanIndex.{u}) :
    finiteSpanDecode (finiteSpanCode x) = x := by
  rcases x with ⟨x⟩
  cases x <;> rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
