module

public import SerrePositivity.EInfinity.Hammock.WordAppend

/-!
# 連結語の写像の元の列の像

概要：連結写像の像は左右の列で元の各写像の像を回収し、単射性を保つ。
方針：有限順序の左右の部分に分け、元の列番号の計算式を使う。
規約：空語も含め、元の列番号を保持する。
使われ方：語の両端への列の追加と proper 性の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

variable {a b c d : Word} (f : a ⟶ c) (g : b ⟶ d)

lemma appendMap_injective (hf : Function.Injective f.orderHom)
    (hg : Function.Injective g.orderHom) : Function.Injective (appendMap f g).orderHom := by
  intro i j h
  cases i using Fin.addCases with
  | left i =>
    cases j using Fin.addCases with
    | left j =>
      rw [appendMap_left, appendMap_left] at h
      have he : (f.orderHom i).val = (f.orderHom j).val :=
        congrArg (fun k : Fin (c.length + d.length) => k.val) h
      exact congrArg (fun k : Fin a.length => k.castAdd b.length)
        (hf (Fin.ext he))
    | right j =>
      rw [appendMap_left, appendMap_right] at h
      have he := congrArg Fin.val h
      have := (f.orderHom i).isLt
      dsimp at he
      omega
  | right i =>
    cases j using Fin.addCases with
    | left j =>
      rw [appendMap_right, appendMap_left] at h
      have he := congrArg Fin.val h
      have := (f.orderHom j).isLt
      dsimp at he
      omega
    | right j =>
      rw [appendMap_right, appendMap_right] at h
      have he : g.orderHom i = g.orderHom j := by
        apply Fin.ext
        have he := congrArg Fin.val h
        dsimp at he
        omega
      exact congrArg (fun k : Fin b.length => k.natAdd a.length) (hg he)

lemma appendMap_range_left (j : Fin c.length) :
    j.castAdd d.length ∈ Set.range (appendMap f g).orderHom ↔ j ∈ Set.range f.orderHom := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i =>
      rw [appendMap_left] at hi
      have he : (f.orderHom i).val = j.val :=
        congrArg (fun k : Fin (c.length + d.length) => k.val) hi
      exact ⟨i, Fin.ext he⟩
    | right i =>
      rw [appendMap_right] at hi
      have he := congrArg Fin.val hi
      have := j.isLt
      dsimp at he
      omega
  · rintro ⟨i, rfl⟩
    exact ⟨i.castAdd b.length, appendMap_left f g i⟩

lemma appendMap_range_right (j : Fin d.length) :
    j.natAdd c.length ∈ Set.range (appendMap f g).orderHom ↔ j ∈ Set.range g.orderHom := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.addCases with
    | left i =>
      rw [appendMap_left] at hi
      have he := congrArg Fin.val hi
      have := (f.orderHom i).isLt
      dsimp at he
      omega
    | right i =>
      rw [appendMap_right] at hi
      refine ⟨i, Fin.ext ?_⟩
      have he := congrArg Fin.val hi
      dsimp at he
      omega
  · rintro ⟨i, rfl⟩
    exact ⟨i.natAdd a.length, appendMap_right f g i⟩

end SerrePositivity.EInfinity.Hammock.Word
