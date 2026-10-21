module

public import SerrePositivity.EInfinity.Hammock.UnmarkedGeneratorColumns
public import Mathlib.Data.Finset.Max

/-!
# 元の最初の非指定生成文字を持つ列

概要：非指定文字を持つ最初の列を選び、その前の全列の指定性と全行での位置の一致を得る。
方針：元の有限の列番号の最小元と、全縦射での文字列の不変性を使う。
規約：列の元の番号・向き・全行を保持する。
使われ方：全語の指定 prefix と残りの hammock の抽出。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
open CategoryTheory SimplicialLocalization

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {w : Word} {X Y : Paths C}

def nonemptyColumns (S : Zigzag W.paths w X Y) : Finset (Fin w.length) := by
  classical
  exact Finset.univ.filter (fun j => column W S j ≠ [])

lemma mem_nonemptyColumns (S : Zigzag W.paths w X Y) (j : Fin w.length) :
    j ∈ nonemptyColumns W S ↔ column W S j ≠ [] := by
  classical
  simp [nonemptyColumns]

lemma nonemptyColumns_nonempty (S : Zigzag W.paths w X Y)
    (h : ∃ j, column W S j ≠ []) : (nonemptyColumns W S).Nonempty := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, (mem_nonemptyColumns W S j).2 hj⟩

def firstColumn (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ []) : Fin w.length :=
  (nonemptyColumns W S).min' (nonemptyColumns_nonempty W S h)

lemma firstColumn_nonempty (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ []) :
    column W S (firstColumn W S h) ≠ [] :=
  (mem_nonemptyColumns W S _).1 (Finset.min'_mem _ _)

lemma firstColumn_le (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ [])
    (j : Fin w.length) (hj : column W S j ≠ []) : firstColumn W S h ≤ j :=
  Finset.min'_le _ j ((mem_nonemptyColumns W S j).2 hj)

lemma before_firstColumn_empty (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ [])
    (j : Fin w.length) (hj : j < firstColumn W S h) : column W S j = [] := by
  classical
  by_contra he
  exact (not_le_of_gt hj) (firstColumn_le W S h j he)

lemma before_firstColumn_mem (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ [])
    (j : Fin w.length) (hj : j < firstColumn W S h) : W.paths (S.arrow j) :=
  (GeneratorWord.erase_eq_nil_iff W (S.arrow j)).1 (before_firstColumn_empty W S h j hj)

lemma firstColumn_forward (S : Zigzag W.paths w X Y) (h : ∃ j, column W S j ≠ []) :
    w.direction (firstColumn W S h) = .forward := by
  cases hi : w.direction (firstColumn W S h) with
  | forward => rfl
  | backward => exact (firstColumn_nonempty W S h (column_backward W S _ hi)).elim

lemma firstColumn_hom {S T : Zigzag W.paths w X Y} (f : S ⟶ T)
    (hS : ∃ j, column W S j ≠ []) (hT : ∃ j, column W T j ≠ []) :
    firstColumn W S hS = firstColumn W T hT := by
  apply le_antisymm
  · apply firstColumn_le W S hS
    intro he
    exact firstColumn_nonempty W T hT ((column_hom W f _).symm.trans he)
  · apply firstColumn_le W T hT
    intro he
    exact firstColumn_nonempty W S hS ((column_hom W f _).trans he)

lemma firstColumn_row {n : SimplexCategoryᵒᵖ} (τ : (graph W.paths w X Y).obj n)
    (k : Fin (n.unop.len + 1)) (h0 : ∃ j, column W (τ.obj 0) j ≠ [])
    (hk : ∃ j, column W (τ.obj k) j ≠ []) :
    firstColumn W (τ.obj 0) h0 = firstColumn W (τ.obj k) hk :=
  firstColumn_hom W (τ.map (homOfLE (Fin.zero_le k))) h0 hk

lemma before_firstColumn_row_mem {n : SimplexCategoryᵒᵖ}
    (τ : (graph W.paths w X Y).obj n) (h0 : ∃ j, column W (τ.obj 0) j ≠ [])
    (k : Fin (n.unop.len + 1)) (j : Fin w.length) (hj : j < firstColumn W (τ.obj 0) h0) :
    W.paths ((τ.obj k).arrow j) := by
  apply (GeneratorWord.erase_eq_nil_iff W ((τ.obj k).arrow j)).1
  change column W (τ.obj k) j = []
  rw [column_row W τ k j]
  exact before_firstColumn_empty W (τ.obj 0) h0 j hj

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators
