module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarSubsetInclusions
public import SerrePositivity.InfinityCategories.DGNerve.LastVertexReplacementData

/-!
概要：元の coherent 単体の末端に、実 bar の包含係数を持つ対象を加える。
方針：末端への各射を非空の先頭部分集合の閉包含とし、元の先頭面を保持する。
規約：これは方程式を課す前のデータであり、bar の MC を仮定しない。
使われ方：二次元以上の列の MC を Bianchi 恒等式へ帰着する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))


def dgCoherentBarBianchiLabel {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hJ : 2 ≤ J.card)
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ)) : dgCoherentBarIndex I :=
  dgCoherentBarSubsetLabel σ (PinchedHom.withoutLast J)
    ((PinchedHom.withoutLast J).card - 1) (by
      have := Finset.card_pos.mpr (PinchedHom.withoutLast_nonempty hJ (hb ▸ J.max'_mem _))
      omega)


lemma dgCoherentBarBianchiLabel_withLast {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    dgCoherentBarBianchiLabel σ (PinchedHom.withLast J) (PinchedHom.two_withLast hJ)
      (PinchedHom.max_withLast J _) = dgCoherentBarSubsetLabel σ J r hc := by
  unfold dgCoherentBarBianchiLabel
  simp only [PinchedHom.withoutLast_withLast]
  have hr : J.card - 1 = r := by omega
  cases hr
  rfl

def dgCoherentBarBianchiOld {n : ℕ} (σ : I _⦋n⦌) :
    DGNerve.Simplex R (RightModule R D) (n + 1) :=
  (coherentDiagramSimplex F σ).pullback (Fin.last n).predAboveOrderHom

def dgCoherentBarBianchiEndHom {n : ℕ} (σ : I _⦋n⦌) :
    SimplexData.LastReplacementHom (dgCoherentBarBianchiOld R D F σ).toSimplexData
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) := by
  intro J a k hJ ha hb hk
  have hlast : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  let K := PinchedHom.withoutLast J
  have hK : K.Nonempty := PinchedHom.withoutLast_nonempty hJ hlast
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  have hmin : (K.min' hK).castSucc = a :=
    (PinchedHom.min_withoutLast J hJ hlast).trans ha.symm
  have hsrc : (coherentDiagramSimplex F σ).obj (K.min' hK) =
      (dgCoherentBarBianchiOld R D F σ).obj a := by
    rw [← hmin]
    change (coherentDiagramSimplex F σ).obj (K.min' hK) =
      (coherentDiagramSimplex F σ).obj ((Fin.last n).predAbove (K.min' hK).castSucc)
    rw [Fin.predAbove_last_castSucc]
  have hdeg : -(r : ℤ) = k := by
    have hcard := PinchedHom.card_withoutLast J hlast
    change J.card = K.card + 1 at hcard
    omega
  exact (gradedHomTransportWithHEq (A := R) (D := RightModule R D) hsrc rfl hdeg
    (dgCoherentBarSubsetInclusion R D F σ K r hc hK)).val



lemma dgCoherentBarBianchiEndHom_heq {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (dgCoherentBarBianchiEndHom R D F σ J a k hJ ha hb hk)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarBianchiLabel σ J hJ hb)) := by
  unfold dgCoherentBarBianchiEndHom
  exact (gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property.trans
    (dgCoherentBarSubsetInclusion_heq R D F σ _ _ _ _)

private lemma barTransport_closed
    {M N M' N' : RightModule R D} {k l : ℤ}
    (hx : M = M') (hy : N = N') (hk : k = l)
    (f : GradedHom R M N k) (hf : differential R f = 0) :
    differential R (D := RightModule R D) (x := M') (y := N')
      (gradedHomTransportWithHEq (A := R) (D := RightModule R D) hx hy hk f).val = 0 := by
  cases hx
  cases hy
  cases hk
  exact hf

lemma dgCoherentBarBianchiEndHom_d {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    differential R (D := RightModule R D)
      (x := (dgCoherentBarBianchiOld R D F σ).obj a)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBianchiEndHom R D F σ J a k hJ ha hb hk) = 0 := by
  unfold dgCoherentBarBianchiEndHom
  apply barTransport_closed
  exact dgCoherentBarSubsetInclusion_d R D F σ _ _ _ _

def dgCoherentBarBianchiData {n : ℕ} (σ : I _⦋n⦌) :
    SimplexData R (RightModule R D) (n + 1) :=
  SimplexData.lastReplacement (dgCoherentBarBianchiOld R D F σ).toSimplexData
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarBianchiEndHom R D F σ)

lemma dgCoherentBarBianchiData_old_equation {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hJ : Fin.last (n + 1) ∉ J) :
    (dgCoherentBarBianchiData R D F σ).Equation J :=
  SimplexData.lastReplacement_equation_old (dgCoherentBarBianchiOld R D F σ)
    _ (dgCoherentBarBianchiEndHom R D F σ) J hJ



lemma dgCoherentBarBianchiData_last_hom_heq {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarBianchiData R D F σ).hom J a (Fin.last (n + 1)) k hJ ha hb hk)
      (dgCoherentBarShiftedInclusion R D F (dgCoherentBarBianchiLabel σ J hJ hb)) :=
  (SimplexData.lastReplacement_hom_last (dgCoherentBarBianchiOld R D F σ).toSimplexData
    _ (dgCoherentBarBianchiEndHom R D F σ) J a k hJ ha hb hk).trans
      (dgCoherentBarBianchiEndHom_heq R D F σ J a k hJ ha hb hk)

lemma dgCoherentBarBianchiData_last_hom_d {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    differential R ((dgCoherentBarBianchiData R D F σ).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) = 0 := by
  let s := dgCoherentBarBianchiOld R D F σ
  let B := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)
  have hx : (dgCoherentBarBianchiData R D F σ).obj a = s.obj a :=
    SimplexData.lastReplacementObj_of_ne s.toSimplexData B a
      (ha ▸ PinchedHom.min_ne_last J hJ)
  have hy : (dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1)) = B :=
    SimplexData.lastReplacementObj_last s.toSimplexData B
  have hh := SimplexData.lastReplacement_hom_last s.toSimplexData B
    (dgCoherentBarBianchiEndHom R D F σ) J a k hJ ha hb hk
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D)
    hx hy rfl _ _ hh
  exact eq_of_heq (hd.trans ((heq_of_eq
    (dgCoherentBarBianchiEndHom_d R D F σ J a k hJ ha hb hk)).trans
      (gradedHom_zero_heq (A := R) (D := RightModule R D) hx.symm hy.symm rfl)))

end SerrePositivity.InfinityCategories
