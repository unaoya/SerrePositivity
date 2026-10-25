module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.SubsetPartialNaturality
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
/-!
概要：末端部分集合のラベルは、その集合上で単射なら自然で、潰れれば退化する。
方針：末端を除く操作と拡張順序写像の像を比較し、部分集合の自然性を適用する。
規約：順序写像全体の単射性に制限しない。
使われ方：native 余錐の全ての退化写像での成分比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarWithoutLast_image_extend {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hl : Fin.last (m + 1) ∈ J) :
    PinchedHom.withoutLast (J.image (PinchedHom.extendOrderHom α)) =
      (PinchedHom.withoutLast J).image α := by
  calc
    _ = PinchedHom.withoutLast
        ((PinchedHom.withLast (PinchedHom.withoutLast J)).image
          (PinchedHom.extendOrderHom α)) :=
      congrArg (fun K => PinchedHom.withoutLast (K.image (PinchedHom.extendOrderHom α)))
        (PinchedHom.withLast_withoutLast J hl).symm
    _ = _ := by rw [PinchedHom.image_withLast_extend, PinchedHom.withoutLast_withLast]

lemma dgCoherentBarInjOn_extend_withoutLast_iff {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hl : Fin.last (m + 1) ∈ J) :
    Set.InjOn (PinchedHom.extendOrderHom α) (J : Set (Fin (m + 2))) ↔
      Set.InjOn α (PinchedHom.withoutLast J : Set (Fin (m + 1))) := by
  rw [← PinchedHom.injOn_extend_withLast_iff α (PinchedHom.withoutLast J),
    PinchedHom.withLast_withoutLast J hl]

variable {I : SSet.{u}}

lemma dgCoherentBarBianchiLabel_map_of_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hJ : 2 ≤ J.card) (hb : Fin.last (m + 1) = J.max' (Index.nonempty hJ))
    (hi : Set.InjOn (PinchedHom.extendOrderHom α) (J : Set (Fin (m + 2))))
    (hJ' : 2 ≤ (J.image (PinchedHom.extendOrderHom α)).card)
    (hb' : Fin.last (n + 1) = (J.image (PinchedHom.extendOrderHom α)).max'
      (Index.nonempty hJ')) :
    dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op s) J hJ hb =
      dgCoherentBarBianchiLabel s (J.image (PinchedHom.extendOrderHom α)) hJ' hb' := by
  have hl : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  have hiK := (dgCoherentBarInjOn_extend_withoutLast_iff α J hl).mp hi
  have hc : (PinchedHom.withoutLast J).card = (PinchedHom.withoutLast J).card - 1 + 1 := by
    have := Finset.card_pos.mpr (PinchedHom.withoutLast_nonempty hJ hl)
    omega
  have h := dgCoherentBarSubsetLabel_map_of_injOn s α (PinchedHom.withoutLast J) hiK
    ((PinchedHom.withoutLast J).card - 1) hc
  simpa only [dgCoherentBarBianchiLabel, dgCoherentBarWithoutLast_image_extend α J hl,
    Finset.card_image_of_injOn hiK] using h

lemma dgCoherentBarBianchiLabel_degenerate_of_not_injOn {m n : ℕ} (s : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (J : Finset (Fin (m + 2)))
    (hJ : 2 ≤ J.card) (hb : Fin.last (m + 1) = J.max' (Index.nonempty hJ))
    (hi : ¬Set.InjOn (PinchedHom.extendOrderHom α) (J : Set (Fin (m + 2)))) :
    (dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op s) J hJ hb).2 ∈
      I.degenerate (dgCoherentBarBianchiLabel
        (I.map (SimplexCategory.mkHom α).op s) J hJ hb).1 := by
  have hl : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  exact dgCoherentBarSubsetLabel_degenerate_of_not_injOn s α (PinchedHom.withoutLast J)
    (hi ∘ (dgCoherentBarInjOn_extend_withoutLast_iff α J hl).mpr)
    ((PinchedHom.withoutLast J).card - 1) (by
      have := Finset.card_pos.mpr (PinchedHom.withoutLast_nonempty hJ hl); omega)

end SerrePositivity.InfinityCategories
