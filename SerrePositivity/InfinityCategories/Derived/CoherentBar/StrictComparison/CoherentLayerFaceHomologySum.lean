module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentSignedLayerFaceColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.DegreeOneHomologyLinear

/-!
概要：実一次層の列のホモロジー射は符号つき実面列の交代和である。
方針：元の全 Hom の有限和公式を評価し、次数一ホモロジー射の整数線形性を使う。
規約：実列の内部閉性を保持する。
使われ方：通常の非退化ホモロジー bar の微分との比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarLayerFaceCochain {n : ℕ} (s : I _⦋n + 1⦌) (i : Fin (n + 2)) (x : D) :
    Cochain ((moduleEvaluation R D x).obj (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)) 1 :=
  (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
      (dgCoherentBarSignedLayerFace R D G s i)

lemma dgCoherentBarLayerFaceCochain_closed {n : ℕ} (s : I _⦋n + 1⦌)
    (i : Fin (n + 2)) (x : D) :
    δ 1 2 (dgCoherentBarLayerFaceCochain R D G s i x) = 0 := by
  have h := moduleHomElement_d_π R D 1 2 (dgCoherentBarSignedLayerFace R D G s i) x
  rw [dgCoherentBarSignedLayerFace_d, map_zero] at h
  exact h.symm

def dgCoherentBarFirstColumnCochain {n : ℕ} (s : I _⦋n + 1⦌) (x : D) :
    Cochain ((moduleEvaluation R D x).obj (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)) 1 :=
  (moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
      (dgCoherentBarFirstLayerColumn R D G s)

lemma dgCoherentBarFirstColumnCochain_closed {n : ℕ} (s : I _⦋n + 1⦌) (x : D) :
    δ 1 2 (dgCoherentBarFirstColumnCochain R D G s x) = 0 := by
  have h := moduleHomElement_d_π R D 1 2 (dgCoherentBarFirstLayerColumn R D G s) x
  rw [dgCoherentBarFirstLayerColumn_d, map_zero] at h
  exact h.symm

lemma dgCoherentBarFirstColumnHomology_sum {n : ℕ} (s : I _⦋n + 1⦌) (x : D) (q : ℤ) :
    dgDegreeOneHomologyMap R (dgCoherentBarFirstColumnCochain R D G s x)
      (dgCoherentBarFirstColumnCochain_closed R D G s x) q =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      dgDegreeOneHomologyMap R (dgCoherentBarLayerFaceCochain R D G s i x)
        (dgCoherentBarLayerFaceCochain_closed R D G s i x) q := by
  apply dgDegreeOneHomologyMap_linearCombination R _ _ (fun i : Fin (n + 2) => (-1 : ℤ) ^ i.val)
    (fun i => dgCoherentBarLayerFaceCochain R D G s i x)
    (fun i => dgCoherentBarLayerFaceCochain_closed R D G s i x) q
  dsimp only [dgCoherentBarFirstColumnCochain, dgCoherentBarLayerFaceCochain]
  rw [dgCoherentBarFirstLayerColumn_eq_sum, map_sum]
  simp only [map_zsmul]
  let K := (moduleEvaluation R D x).obj (dgCoherentBarFamily R D G ⟨n + 1, s⟩)
  let L := (moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G n)
  let ev : Cochain K L 1 →+ (K.X q ⟶ L.X (q + 1)) :=
    { toFun z := z.v q (q + 1) rfl
      map_zero' := Cochain.zero_v _ _ _
      map_add' a b := Cochain.add_v a b _ _ _ }
  let b : Fin (n + 2) → Cochain K L 1 := fun i =>
    (moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarLayerGraded R D G n)) x).f 1
        (dgCoherentBarSignedLayerFace R D G s i)
  change ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • b i) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • ev (b i)
  rw [map_sum]
  simp only [map_zsmul]

end SerrePositivity.InfinityCategories
