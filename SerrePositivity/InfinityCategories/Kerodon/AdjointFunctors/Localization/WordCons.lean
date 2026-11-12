module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word

/-!
# 元の向き付き語への先頭の一文字の追加

概要：長さ帰納に使う先頭の一列と残りの語の表示を与える。
方針：Fin.cases で先頭と残りの元の向きを保持する。
規約：頂点と列は左から右へ番号を付ける。
使われ方：DK9.4・10.3・5.7の元の全語の図式の帰納。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

def cons (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := ⟨w.length + 1, Fin.cases d w.direction⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cons)


lemma cons_length (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (cons d w).length = w.length + 1 := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cons_length)


lemma cons_direction_zero (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (cons d w).direction (0 : Fin (w.length + 1)) = d := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cons_direction_zero)


lemma cons_direction_succ (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) :
    (cons d w).direction i.succ = w.direction i := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (cons_direction_succ)


lemma eq_empty_of_length_zero (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (h : w.length = 0) : w = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty := by
  rcases w with ⟨n, δ⟩
  dsimp at h
  subst n
  have hd : δ = Fin.elim0 := funext (fun i => Fin.elim0 i)
  cases hd
  rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (eq_empty_of_length_zero)


lemma exists_cons_of_length_succ (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (n : ℕ) (h : w.length = n + 1) :
    ∃ d v, w = cons d v := by
  rcases w with ⟨m, δ⟩
  dsimp at h
  subst m
  refine ⟨δ 0, ⟨n, fun i => δ i.succ⟩, ?_⟩
  apply congrArg (fun f => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.mk (n + 1) f)
  funext i
  cases i using Fin.cases <;> rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (exists_cons_of_length_succ)


@[elab_as_elim] lemma induction_on {P : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word → Prop} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (h0 : P _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty)
    (hs : ∀ d v, P v → P (cons d v)) : P w := by
  have aux : ∀ n, ∀ v : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word, v.length = n → P v := by
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (induction_on)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
