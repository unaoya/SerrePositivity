module

public import SerrePositivity.EInfinity.Hammock.WordCutFactorMaps
public import SerrePositivity.EInfinity.Hammock.WordCutFactorVertices
public import SerrePositivity.EInfinity.Hammock.WordCut

/-!
# 元の prefix 制限射の全切断位置

概要：切断した prefix の前の全頂点では、制限射の cut が元の cut に一致する。
方針：元の初期区間の特徴付けと切断列より左の像の単調性を使う。
規約：元の列番号と空 fiber を保持する。
使われ方：prefix 全図式の語の作用への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word.CutFactor
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (i : Fin a.length) (hi : a.direction i = .forward)

lemma cut_le_column (t : Fin (b.length + 1)) (ht : t.val ≤ (f.orderHom i).val) :
    (f.cut t).val ≤ i.val := by
  apply (Hom.cutNat_le_iff f t i.val).2
  intro k hk
  by_contra hki
  have hm := f.orderHom.monotone (show i ≤ k by omega)
  change (f.orderHom i).val ≤ (f.orderHom k).val at hm
  omega

lemma prefix_cut (k : Fin ((ColumnSplit.before b (f.orderHom i)).length + 1)) :
    ((prefixMap f i hi).cut
      (leftVertex (ColumnSplit.before b (f.orderHom i)) (single .forward) k)).val =
      (f.cut (prefixVertex b (f.orderHom i) k)).val := by
  let t := prefixVertex b (f.orderHom i) k
  let s := leftVertex (ColumnSplit.before b (f.orderHom i)) (single .forward) k
  have ht : t.val ≤ (f.orderHom i).val := Nat.le_of_lt_succ k.isLt
  apply Nat.le_antisymm
  · apply (Hom.cutNat_le_iff (prefixMap f i hi) s _).2
    intro l hl
    exact (f.lt_cut_iff t (prefixColumn a i l)).2 hl
  · apply (Hom.cutNat_le_iff f t _).2
    intro l hl
    have hli : l.val < i.val := by
      by_contra hn
      have hm := f.orderHom.monotone (show i ≤ l by omega)
      change (f.orderHom i).val ≤ (f.orderHom l).val at hm
      omega
    let r : Fin (prefixWord a i).length := ⟨l.val, by change l.val < i.val + 1; omega⟩
    have he : prefixColumn a i r = l := Fin.ext rfl
    have hr : ((prefixMap f i hi).orderHom r).val < s.val := by
      change (f.orderHom (prefixColumn a i r)).val < t.val
      rw [he]
      exact hl
    exact ((prefixMap f i hi).lt_cut_iff s r).2 hr

end SerrePositivity.EInfinity.Hammock.Word.CutFactor
