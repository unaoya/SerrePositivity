module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeSimplices
/-!
概要：余錐単体の全末端成分を、同じ元の部分単体ラベルの native 列へ戻す。
方針：先頭部分集合の最小点と次数を計算し、Bianchi の既存成分比較を後合成する。
規約：端点と次数の輸送を異種等号で明示し、退化ラベルも除外しない。
使われ方：全単体作用に対する自然性と、native Hom 普遍性の座標比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarBianchiLabel_source {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) :
    (dgCoherentBarBianchiData R D F s).obj a =
      dgCoherentBarSource R D F (dgCoherentBarBianchiLabel s J hJ hb) := by
  have hl : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  have hK := PinchedHom.withoutLast_nonempty hJ hl
  have hm : ((PinchedHom.withoutLast J).min' hK).castSucc = a :=
    (PinchedHom.min_withoutLast J hJ hl).trans ha.symm
  rw [← hm, dgCoherentBarBianchiData_obj_castSucc]
  exact (dgCoherentBarSubsetLabel_source R D F s (PinchedHom.withoutLast J)
    ((PinchedHom.withoutLast J).card - 1) (by
      have := Finset.card_pos.mpr hK; omega) hK).symm

lemma dgCoherentBarBianchiLabel_degree {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hJ : 2 ≤ J.card)
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ))
    (k : ℤ) (hk : k = 2 - (J.card : ℤ)) :
    k = -((dgCoherentBarBianchiLabel s J hJ hb).1 : ℤ) := by
  have hl : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  have hc := PinchedHom.card_withoutLast J hl
  have hp := Finset.card_pos.mpr (PinchedHom.withoutLast_nonempty hJ hl)
  change k = -(((PinchedHom.withoutLast J).card - 1 : ℕ) : ℤ)
  omega

lemma dgCoherentBarNativeSimplexData_last_hom_heq {n : ℕ} (s : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarNativeSimplexData R D F hMC s).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk)
      (dgCoherentBarNativeColumn R D F hMC (dgCoherentBarBianchiLabel s J hJ hb)) := by
  have hx := dgCoherentBarBianchiLabel_source R D F s J a hJ ha hb
  have hy := dgCoherentBarBianchiData_obj_last R D F s
  have hdeg := dgCoherentBarBianchiLabel_degree s J hJ hb k hk
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy rfl hdeg rfl hdeg _ _ _ _
    (dgCoherentBarNativeBianchiProjection_heq R D F hMC s)
    (dgCoherentBarBianchiData_last_hom_heq R D F s J a k hJ ha hb hk)
    (add_zero k) (add_zero _)
  refine (dgCoherentBarPostLastData_hom_last (dgCoherentBarBianchiData R D F s)
    (dgCoherentBarNormalizedModule R D F hMC)
    (dgCoherentBarNativeBianchiProjection R D F hMC s) J a k hJ ha hb hk).trans
      (hc.trans (heq_of_eq ?_))
  exact dgCoherentBarNormalizedTargetProjection_compose R D F hMC
    (dgCoherentBarSource R D F (dgCoherentBarBianchiLabel s J hJ hb)) _ _

end SerrePositivity.InfinityCategories
