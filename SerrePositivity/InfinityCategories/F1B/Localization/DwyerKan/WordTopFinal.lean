module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordTopStage
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordFactorization

/-!
# 非交互の最大長の語を除く包含の Final 性

概要：前段階の全語と最大長の交互方向語だけで、元の段階の余極限を計算できる。
方針：StructuredArrow の非空性と連結性を基本合成の元の可換余錐で証明する。
規約：包含は元の全部分圏の包含であり、選んだ別の同値で代用しない。
使われ方：段階の pushout の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock.Word
open CategoryTheory

lemma exists_adjacent_of_not_alternating {k : ℕ} (d : Fin (k + 2) → Direction)
    (h : ¬ IsAlternating (⟨k + 2, d⟩ : Word)) :
    ∃ p : Fin (k + 1), d p.castSucc = d p.succ := by
  simp only [IsAlternating, not_forall, not_not] at h
  obtain ⟨i, j, hij, hd⟩ := h
  let p : Fin (k + 1) := ⟨i.val, by have := j.isLt; omega⟩
  have hi : p.castSucc = i := Fin.ext rfl
  have hj : p.succ = j := Fin.ext hij.symm
  exact ⟨p, by rw [hi, hj]; exact hd⟩

lemma topStage_comma_connected (n : ℕ) (a : LengthBounded n) :
    IsConnected (StructuredArrow a (topStageInclusion n)) := by
  by_cases ha : topStageProperty n a
  · let t : StructuredArrow a (topStageInclusion n) :=
      StructuredArrow.mk (Y := (⟨a, ha⟩ : TopStage n)) (𝟙 a)
    let : Nonempty (StructuredArrow a (topStageInclusion n)) := ⟨t⟩
    have ht (s : StructuredArrow a (topStageInclusion n)) : Nonempty (t ⟶ s) :=
      ⟨StructuredArrow.homMk (ObjectProperty.homMk s.hom) (by
        change (𝟙 a) ≫ s.hom = s.hom
        exact Category.id_comp _)⟩
    apply zigzag_isConnected
    intro s s'
    obtain ⟨hs⟩ := ht s
    obtain ⟨hs'⟩ := ht s'
    exact Zigzag.of_inv_hom hs hs'
  · cases a with
    | mk aw hn =>
      cases aw with
      | mk l d =>
        cases l with
        | zero =>
          apply False.elim
          apply ha
          right
          intro i
          exact Fin.elim0 i
        | succ l =>
          cases l with
          | zero =>
            apply False.elim
            apply ha
            right
            intro i j hij
            have hi := i.isLt
            have hj := j.isLt
            change i.val < 1 at hi
            change j.val < 1 at hj
            change j.val = i.val + 1 at hij
            omega
          | succ k =>
            obtain ⟨p, hp⟩ := exists_adjacent_of_not_alternating d (fun h => ha (Or.inr h))
            let : Nonempty (StructuredArrow (⟨⟨k + 2, d⟩, hn⟩ : LengthBounded n)
                (topStageInclusion n)) := ⟨topMergeArrow n d hn p hp⟩
            have ht (t : StructuredArrow (⟨⟨k + 2, d⟩, hn⟩ : LengthBounded n)
                (topStageInclusion n)) :
                ∃ q : Fin (k + 1), ∃ hq : d q.castSucc = d q.succ,
                  Nonempty (topMergeArrow n d hn q hq ⟶ t) := by
              let f : (⟨k + 2, d⟩ : Word) ⟶ t.right.obj.obj := t.hom.hom
              have hf : ¬ Function.Injective f.orderHom :=
                not_injective_of_not_top (⟨⟨k + 2, d⟩, hn⟩ : LengthBounded n) ha t.right f
              have hq : ∃ q : Fin (k + 1),
                  f.orderHom q.castSucc = f.orderHom q.succ := by
                simpa only [Fin.orderHom_injective_iff, not_forall, not_not] using hf
              obtain ⟨q, hq⟩ := hq
              let hc := adjacent_color_of_image_eq d f q hq
              obtain ⟨g, hg⟩ := factorMerge d f q hq
              refine ⟨q, hc, ⟨StructuredArrow.homMk
                (ObjectProperty.homMk (ObjectProperty.homMk g)) ?_⟩⟩
              apply ObjectProperty.hom_ext
              exact hg
            apply zigzag_isConnected
            intro s t
            obtain ⟨q, hq, ⟨hs⟩⟩ := ht s
            obtain ⟨r, hr, ⟨ht'⟩⟩ := ht t
            exact (Zigzag.of_inv hs).trans
              ((topMergeArrow_zigzag n d hn q r hq hr).trans (Zigzag.of_hom ht'))

/-- 元の全部分圏の包含の Final 性。大域 instance には登録しない。 -/
lemma topStageFinal (n : ℕ) : (topStageInclusion n).Final where
  out a := topStage_comma_connected n a

end SerrePositivity.EInfinity.Hammock.Word
