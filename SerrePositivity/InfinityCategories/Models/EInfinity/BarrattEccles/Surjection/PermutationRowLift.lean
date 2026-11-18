module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.VerticalRows

/-!
模型。文献の定義との比較は後で
# 実際の置換列と選択長さから元の行列を復元する

概要：Berger–Fresse §1.5.7 の切り出した成分行を元の置換と行長の列として読む。
方針：一致する行の列と元の選択長さを zip し、各行を比較する。
規約：置換行自体を復元候補で置き換えず、元の頂点列を使う。
使われ方：成分の抽出証跡を実際の固定外側合成へ転送する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：元の置換の行表示と選択長さの zip は同じ抽出行列（BF §1.5.7）。
方針：置換と行を同時に先頭から比較する。
規約：行表示の列の一致から列の長さの一致も従う。
使われ方：元の区間証明書の行列を置換と長さの列に移す。 -/
lemma permutationRows_zip {n : ℕ} (vs : List (Equiv.Perm (Fin n)))
    (rs : List (List (Fin n) × ℕ))
    (h : vs.map (fun τ => List.ofFn τ.symm) = rs.map Prod.fst) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows (vs.zip (rs.map Prod.snd)) = rs := by
  induction vs generalizing rs with
  | nil =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      simp only [List.map_nil, List.map_cons] at h
      cases h
  | cons τ vs ih =>
    cases rs with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at h
    | cons r rs =>
      obtain ⟨row, length⟩ := r
      have he := List.cons.inj h
      change (List.ofFn τ.symm, length) :: _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.permutationRows (vs.zip (rs.map Prod.snd)) =
        (row, length) :: rs
      have hhead : List.ofFn τ.symm = row := he.1
      rw [hhead, ih rs he.2]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
