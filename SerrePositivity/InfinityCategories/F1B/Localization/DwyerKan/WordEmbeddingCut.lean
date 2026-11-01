module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordCut
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Zigzag

/-!
# 単射な語の射の元の列における切断

概要：単射な語の射の各像の列の前後で、切断は元の列の前後を厳密に回収する。
方針：左側の全列による切断の特徴付けと、単射な単調写像の狭義単調性を使う。
規約：空語を含み、余分な射影や語の retraction は選ばない。
使われ方：語の包含による元の zigzag と graph の単射性。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.Hammock.Word.Hom
open CategoryTheory

variable {a b : Word} (f : a ⟶ b) (hf : Function.Injective f.orderHom)
include hf

lemma cut_image_castSucc (i : Fin a.length) :
    f.cut (f.orderHom i).castSucc = i.castSucc := by
  apply vertex_ext
  intro j
  rw [lt_cut_iff]
  exact (f.orderHom.monotone.strictMono_of_injective hf).lt_iff_lt

lemma cut_image_succ (i : Fin a.length) : f.cut (f.orderHom i).succ = i.succ := by
  apply vertex_ext
  intro j
  rw [lt_cut_iff]
  change (f.orderHom j).val < (f.orderHom i).val + 1 ↔ j.val < i.val + 1
  simpa only [Nat.lt_add_one_iff, Fin.le_iff_val_le_val] using
    (f.orderHom.monotone.strictMono_of_injective hf).le_iff_le (a := j) (b := i)

/-- 包含に沿う切断は元の全頂点を被覆する。 -/
lemma cut_surjective : Function.Surjective f.cut := by
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨0, cut_zero f⟩
  | succ i => exact ⟨(f.orderHom i).succ, cut_image_succ f hf i⟩

lemma cut_image_source (i : Fin a.length) :
    f.cut (b.source (f.orderHom i)) = a.source i := by
  unfold Word.source
  rw [f.direction_eq i]
  cases a.direction i
  · exact cut_image_castSucc f hf i
  · exact cut_image_succ f hf i

lemma cut_image_target (i : Fin a.length) :
    f.cut (b.target (f.orderHom i)) = a.target i := by
  unfold Word.target
  rw [f.direction_eq i]
  cases a.direction i
  · exact cut_image_succ f hf i
  · exact cut_image_castSucc f hf i

end SerrePositivity.EInfinity.Hammock.Word.Hom
