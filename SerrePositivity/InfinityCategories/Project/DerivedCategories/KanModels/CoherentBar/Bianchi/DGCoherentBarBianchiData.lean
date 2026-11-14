module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Structure.DGCoherentBarSubsetInclusions
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LastVertexReplacementData

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))


def dgCoherentBarBianchiLabel {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hJ : 2 ≤ J.card)
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarIndex I :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J).card - 1) (by
      have := Finset.card_pos.mpr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ (hb ▸ J.max'_mem _))
      omega)


lemma dgCoherentBarBianchiLabel_withLast {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    dgCoherentBarBianchiLabel σ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.two_withLast hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.max_withLast J _) = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel σ J r hc := by
  unfold dgCoherentBarBianchiLabel
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_withLast]
  have hr : J.card - 1 = r := by omega
  cases hr
  rfl

def dgCoherentBarBianchiOld {n : ℕ} (σ : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) (n + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).pullback (Fin.last n).predAboveOrderHom

def dgCoherentBarBianchiEndHom {n : ℕ} (σ : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LastReplacementHom (dgCoherentBarBianchiOld R D F σ).toSimplexData
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) := by
  intro J a k hJ ha hb hk
  have hlast : Fin.last (n + 1) ∈ J := hb ▸ J.max'_mem _
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast J
  have hK : K.Nonempty := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast_nonempty hJ hlast
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  have hmin : (K.min' hK).castSucc = a :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_withoutLast J hJ hlast).trans ha.symm
  have hsrc : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).obj (K.min' hK) =
      (dgCoherentBarBianchiOld R D F σ).obj a := by
    rw [← hmin]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).obj (K.min' hK) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F σ).obj ((Fin.last n).predAbove (K.min' hK).castSucc)
    rw [Fin.predAbove_last_castSucc]
  have hdeg : -(r : ℤ) = k := by
    have hcard := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.card_withoutLast J hlast
    change J.card = K.card + 1 at hcard
    omega
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D) hsrc rfl hdeg
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetInclusion R D F σ K r hc hK)).val



lemma dgCoherentBarBianchiEndHom_heq {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (dgCoherentBarBianchiEndHom R D F σ J a k hJ ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (dgCoherentBarBianchiLabel σ J hJ hb)) := by
  unfold dgCoherentBarBianchiEndHom
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D) _ _ _ _).property.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetInclusion_heq R D F σ _ _ _ _)

private lemma barTransport_closed
    {M N M' N' : _root_.SerrePositivity.DifferentialGraded.RightModule R D} {k l : ℤ}
    (hx : M = M') (hy : N = N') (hk : k = l)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R M N k) (hf : _root_.SerrePositivity.DifferentialGraded.differential R f = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D) (x := M') (y := N')
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransportWithHEq (A := R) (D := RightModule R D) hx hy hk f).val = 0 := by
  cases hx
  cases hy
  cases hk
  exact hf

lemma dgCoherentBarBianchiEndHom_d {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.differential R (D := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
      (x := (dgCoherentBarBianchiOld R D F σ).obj a)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (dgCoherentBarBianchiEndHom R D F σ J a k hJ ha hb hk) = 0 := by
  unfold dgCoherentBarBianchiEndHom
  apply barTransport_closed
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetInclusion_d R D F σ _ _ _ _

def dgCoherentBarBianchiData {n : ℕ} (σ : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement (dgCoherentBarBianchiOld R D F σ).toSimplexData
    (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (dgCoherentBarBianchiEndHom R D F σ)

lemma dgCoherentBarBianchiData_old_equation {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (hJ : Fin.last (n + 1) ∉ J) :
    (dgCoherentBarBianchiData R D F σ).Equation J :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_equation_old (dgCoherentBarBianchiOld R D F σ)
    _ (dgCoherentBarBianchiEndHom R D F σ) J hJ



lemma dgCoherentBarBianchiData_last_hom_heq {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq ((dgCoherentBarBianchiData R D F σ).hom J a (Fin.last (n + 1)) k hJ ha hb hk)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F (dgCoherentBarBianchiLabel σ J hJ hb)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_hom_last (dgCoherentBarBianchiOld R D F σ).toSimplexData
    _ (dgCoherentBarBianchiEndHom R D F σ) J a k hJ ha hb hk).trans
      (dgCoherentBarBianchiEndHom_heq R D F σ J a k hJ ha hb hk)

lemma dgCoherentBarBianchiData_last_hom_d {n : ℕ} (σ : I _⦋n⦌)
    (J : Finset (Fin (n + 2))) (a : Fin (n + 2)) (k : ℤ)
    (hJ : 2 ≤ J.card) (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : Fin.last (n + 1) = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    _root_.SerrePositivity.DifferentialGraded.differential R ((dgCoherentBarBianchiData R D F σ).hom
      J a (Fin.last (n + 1)) k hJ ha hb hk) = 0 := by
  let s := dgCoherentBarBianchiOld R D F σ
  let B := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)
  have hx : (dgCoherentBarBianchiData R D F σ).obj a = s.obj a :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne s.toSimplexData B a
      (ha ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last J hJ)
  have hy : (dgCoherentBarBianchiData R D F σ).obj (Fin.last (n + 1)) = B :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last s.toSimplexData B
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacement_hom_last s.toSimplexData B
    (dgCoherentBarBianchiEndHom R D F σ) J a k hJ ha hb hk
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D)
    hx hy rfl _ _ hh
  exact eq_of_heq (hd.trans ((heq_of_eq
    (dgCoherentBarBianchiEndHom_d R D F σ J a k hJ ha hb hk)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D) hx.symm hy.symm rfl)))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
