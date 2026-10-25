module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeLabelCoordinates
/-!
概要：任意の先頭部分集合を持つ正規化 native 単体の成分を、その部分単体の列へ戻す。
方針：既存の Bianchi ラベルと withLast の比較を直接適用する。
規約：非退化性を仮定せず、実加群の端点を保持する。
使われ方：高次余錐族の混合成分と native HA 項の後合成比較。
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

lemma dgCoherentBarNativeSimplex_subset_source {n : ℕ} (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (r : ℕ) (hc : K.card = r + 1) (hK : K.Nonempty) :
    (dgCoherentBarNativeSimplex R D F hMC s).obj (K.min' hK).castSucc =
      dgCoherentBarSource R D F (dgCoherentBarSubsetLabel s K r hc) := by
  have h := congrArg (fun t : DGNerve.Simplex R (RightModule R D) n => t.obj (K.min' hK))
    (dgCoherentBarNativeSimplex_front R D F hMC s)
  exact h.trans (dgCoherentBarSubsetLabel_source R D F s K r hc hK).symm

lemma dgCoherentBarNativeSimplex_subset_hom_heq {n : ℕ} (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (r : ℕ) (hc : K.card = r + 1) (hK : K.Nonempty) :
    HEq ((dgCoherentBarNativeSimplex R D F hMC s).hom (PinchedHom.withLast K)
      (K.min' hK).castSucc (Fin.last (n + 1)) (-(r : ℤ)) (PinchedHom.two_withLast hK)
      (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
      (by rw [PinchedHom.card_withLast, hc]; push_cast; omega))
      (dgCoherentBarNativeColumn R D F hMC (dgCoherentBarSubsetLabel s K r hc)) := by
  have h := dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC s (PinchedHom.withLast K)
    (K.min' hK).castSucc (-(r : ℤ)) (PinchedHom.two_withLast hK)
    (PinchedHom.min_withLast hK _) (PinchedHom.max_withLast K _)
    (by rw [PinchedHom.card_withLast, hc]; push_cast; omega)
  rw [dgCoherentBarBianchiLabel_withLast s K r hc hK] at h
  exact h

end SerrePositivity.InfinityCategories
