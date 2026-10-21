module

public import SerrePositivity.EInfinity.Hammock.Word

/-!
# 元の向き付き語への先頭の一文字の追加

概要：長さ帰納に使う先頭の一列と残りの語の表示を与える。
方針：Fin.cases で先頭と残りの元の向きを保持する。
規約：頂点と列は左から右へ番号を付ける。
使われ方：DK9.4・10.3・5.7の元の全語の図式の帰納。
-/

@[expose] public section
namespace SerrePositivity.EInfinity.Hammock.Word

def cons (d : Direction) (w : Word) : Word := ⟨w.length + 1, Fin.cases d w.direction⟩

lemma cons_length (d : Direction) (w : Word) : (cons d w).length = w.length + 1 := rfl

lemma cons_direction_zero (d : Direction) (w : Word) :
    (cons d w).direction (0 : Fin (w.length + 1)) = d := rfl

lemma cons_direction_succ (d : Direction) (w : Word) (i : Fin w.length) :
    (cons d w).direction i.succ = w.direction i := rfl

lemma eq_empty_of_length_zero (w : Word) (h : w.length = 0) : w = empty := by
  rcases w with ⟨n, δ⟩
  dsimp at h
  subst n
  have hd : δ = Fin.elim0 := funext (fun i => Fin.elim0 i)
  cases hd
  rfl

lemma exists_cons_of_length_succ (w : Word) (n : ℕ) (h : w.length = n + 1) :
    ∃ d v, w = cons d v := by
  rcases w with ⟨m, δ⟩
  dsimp at h
  subst m
  refine ⟨δ 0, ⟨n, fun i => δ i.succ⟩, ?_⟩
  apply congrArg (fun f => Word.mk (n + 1) f)
  funext i
  cases i using Fin.cases <;> rfl

@[elab_as_elim] lemma induction_on {P : Word → Prop} (w : Word) (h0 : P empty)
    (hs : ∀ d v, P v → P (cons d v)) : P w := by
  have aux : ∀ n, ∀ v : Word, v.length = n → P v := by
    intro n
    induction n with
    | zero =>
      intro v hv
      simpa only [eq_empty_of_length_zero v hv] using h0
    | succ n ih =>
      intro v hv
      obtain ⟨d, v, rfl⟩ := exists_cons_of_length_succ v n hv
      exact hs d v (ih v (Nat.succ.inj hv))
  exact aux w.length w rfl

end SerrePositivity.EInfinity.Hammock.Word
