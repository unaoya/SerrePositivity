module

public import SerrePositivity.KST.Spectra.AdjacentFacePrism

/-!
概要：隣接二面の prism の各境界面への制限。
方針：切り替え写像の頂点値を比較し、面の穴の位置の算術を使う。
規約：境界面が切り替え位置の前・後・一致の三場合を扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。RelStruct の基点固定条件。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.AdjacentFacePrism

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：切り替え位置より前の面では prism は一つ前の添字の prism を通る。
方針：穴の位置の算術を各頂点の値で検査する。
規約：j<i。
使われ方：Kerodon §3.2.2（Tag 00VJ）。RelStruct の前側の定数面。 -/
theorem face_of_lt {n : ℕ} (i j : Fin (n + 2)) (hji : j < i) :
    stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ map i =
      map (i.pred (Fin.ne_zero_of_lt hji)) ≫ stdSimplex.δ j.castSucc := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply stdSimplex.ext
  intro a
  change (if t a = 0 then i.succ.succAbove (j.succAbove (s a))
      else i.castSucc.succAbove (j.succAbove (s a))) =
    j.castSucc.succAbove (if t a = 0 then (i.pred _).succ.succAbove (s a)
      else (i.pred _).castSucc.succAbove (s a))
  split_ifs <;> apply Fin.ext <;>
    simp only [Fin.succAbove] <;> split_ifs <;>
    simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_pred,
      not_true_eq_false, not_false_eq_true] <;>
    omega

/-- 概要：切り替え位置より後の面では prism は同じ添字を縮めた prism を通る。
方針：後の穴を除いた単調埋め込みの頂点値を比較する。
規約：i<j。
使われ方：Kerodon §3.2.2（Tag 00VJ）。RelStruct の後側の定数面。 -/
theorem face_of_gt {n : ℕ} (i j : Fin (n + 2)) (hij : i < j) :
    stdSimplex.δ j ▷ (Δ[1] : SSet.{u}) ≫ map i =
      map (i.castPred (Fin.ne_last_of_lt hij)) ≫ stdSimplex.δ j.succ := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply stdSimplex.ext
  intro a
  change (if t a = 0 then i.succ.succAbove (j.succAbove (s a))
      else i.castSucc.succAbove (j.succAbove (s a))) =
    j.succ.succAbove (if t a = 0 then (i.castPred _).succ.succAbove (s a)
      else (i.castPred _).castSucc.succAbove (s a))
  split_ifs <;> apply Fin.ext <;>
    simp only [Fin.succAbove] <;> split_ifs <;>
    simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.coe_castPred,
      not_true_eq_false, not_false_eq_true] <;>
    omega

/-- 概要：切り替え位置の面では prism の区間変数は消える。
方針：切り替わる二つの頂点を欠くため、二つの埋め込みは同じ値を取る。
規約：二つの隣接面の共通面へ定数に写る。
使われ方：Kerodon §3.2.2（Tag 00VJ）。PtSimplex の境界定数条件を使う面。 -/
theorem face_self {n : ℕ} (i : Fin (n + 2)) :
    stdSimplex.δ i ▷ (Δ[1] : SSet.{u}) ≫ map i =
      fst (Δ[n] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ stdSimplex.δ i ≫ stdSimplex.δ i.succ := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  apply stdSimplex.ext
  intro a
  change (if t a = 0 then i.succ.succAbove (i.succAbove (s a))
      else i.castSucc.succAbove (i.succAbove (s a))) = i.succ.succAbove (i.succAbove (s a))
  split_ifs
  · rfl
  · apply Fin.ext
    simp only [Fin.succAbove]
    split_ifs <;>
      simp_all only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ, not_true_eq_false] <;> omega

end

end SerrePositivity.KST.Spectra.AdjacentFacePrism
