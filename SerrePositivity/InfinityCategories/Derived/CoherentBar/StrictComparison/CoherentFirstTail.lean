module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarDifferential

/-!
概要：一次 prefix の後尾ラベルは零番の面ラベルである。
方針：元の単体作用素の順序写像を比較する。
規約：raw bar の次元つきラベルの等号を示す。
使われ方：一次辺列を通常の bar の零番の面へ合わせる。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial

lemma dgCoherentBarTail_one_eq_face_zero {I : SSet.{u}} {n : ℕ} (s : I _⦋n + 1⦌) :
    dgCoherentBarTail s 1 (by omega) = dgCoherentBarFace s (0 : Fin (n + 2)) := by
  have h : SimplexCategory.mkHom (dgCoherentBarTailOrder (n + 1) 1 (by omega)) =
      SimplexCategory.δ (0 : Fin (n + 2)) := by
    ext j
    change 1 + j.val = ((0 : Fin (n + 2)).succAbove j).val
    rw [Fin.succAbove_zero, Fin.val_succ]
    omega
  have hh := congrArg (fun f => (⟨n, I.map f.op s⟩ : dgCoherentBarIndex I)) h
  simpa only [dgCoherentBarTail, dgCoherentBarFace, Nat.add_sub_cancel,
    SimplicialObject.δ] using! hh

end SerrePositivity.InfinityCategories
