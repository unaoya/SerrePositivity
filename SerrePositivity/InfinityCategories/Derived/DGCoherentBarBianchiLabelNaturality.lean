module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBianchiFullTerms
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarSubsetNaturality
public import SerrePositivity.InfinityCategories.DGNerve.PinchedReindexIndex

/-!
概要：bar を末端に加えた係数のラベルは、先頭頂点の単射な制限と厳密に両立する。
方針：最終点固定の延長による像から先頭集合を回収し、元の部分単体の自然性を使う。
規約：実単体ラベルの等号を保持する。
使われ方：全体 HA 右辺の比較を任意の部分集合へ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarExtend_injective {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α) :
    Function.Injective (PinchedHom.extendOrderHom α) := by
  have hh := (DGNerve.PinchedHom.injOn_extend_withLast_iff α Finset.univ).mpr hα.injOn
  rw [dgCoherentBar_withLast_univ] at hh
  exact fun a b hab => hh (Finset.mem_univ _) (Finset.mem_univ _) hab

variable {I : SSet.{u}}

lemma dgCoherentBarBianchiLabel_map {m n : ℕ} (σ : I _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (J : Finset (Fin (m + 2))) (hJ : 2 ≤ J.card)
    (hb : Fin.last (m + 1) = J.max' (Index.nonempty hJ))
    (hJ' : 2 ≤ (J.image (PinchedHom.extendOrderHom α)).card)
    (hb' : Fin.last (n + 1) = (J.image (PinchedHom.extendOrderHom α)).max' (Index.nonempty hJ')) :
    dgCoherentBarBianchiLabel (I.map (SimplexCategory.mkHom α).op σ) J hJ hb =
      dgCoherentBarBianchiLabel σ (J.image (PinchedHom.extendOrderHom α)) hJ' hb' := by
  have hLast : Fin.last (m + 1) ∈ J := hb ▸ J.max'_mem _
  have hK : DGNerve.PinchedHom.withoutLast (J.image (PinchedHom.extendOrderHom α)) =
      (DGNerve.PinchedHom.withoutLast J).image α := by
    calc
      _ = DGNerve.PinchedHom.withoutLast
          ((DGNerve.PinchedHom.withLast (DGNerve.PinchedHom.withoutLast J)).image
            (PinchedHom.extendOrderHom α)) :=
        congrArg (fun S => DGNerve.PinchedHom.withoutLast (S.image (PinchedHom.extendOrderHom α)))
          (DGNerve.PinchedHom.withLast_withoutLast J hLast).symm
      _ = _ := by rw [DGNerve.PinchedHom.image_withLast_extend, DGNerve.PinchedHom.withoutLast_withLast]
  have hcard : ((DGNerve.PinchedHom.withoutLast J).image α).card =
      (DGNerve.PinchedHom.withoutLast J).card := Finset.card_image_of_injective _ hα
  have hc : (DGNerve.PinchedHom.withoutLast J).card =
      (DGNerve.PinchedHom.withoutLast J).card - 1 + 1 := by
    have := Finset.card_pos.mpr (DGNerve.PinchedHom.withoutLast_nonempty hJ hLast)
    omega
  have hh := dgCoherentBarSubsetLabel_map σ α hα (DGNerve.PinchedHom.withoutLast J)
    ((DGNerve.PinchedHom.withoutLast J).card - 1) hc
  simpa only [dgCoherentBarBianchiLabel, hK, hcard] using hh

end SerrePositivity.InfinityCategories
