module
public import SerrePositivity.InfinityCategories.DGNerve.CoherentDiagramEdgeBoundary
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarFaceDifferential
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarPrefixDifferential
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarBoundaryTerms
public import Mathlib.Tactic.FinCases
/-!
概要：元の coherent bar の一次元列は MC 方程式を満たす。
方針：二つの終端は頂点列なので二乗項が消え、面と辺 prefix の内部微分も零となる。
規約：任意の元の dg 図式の同じ辺・直和・全 Hom を保持する。
使われ方：全正次元列の MC 証明の最初の場合。
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

lemma dgCoherentBarPrefixBoundary_edge {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    dgCoherentBarPrefixBoundary R D F s 0 h = 0 := by
  unfold dgCoherentBarPrefixBoundary
  rw [coherentDiagramTopBoundary_edge, map_zero]

lemma dgCoherentBarPrefixBlock_edge_d {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarFamily R D F (dgCoherentBarTail s 1 h)))).d 1 2
      (dgCoherentBarPrefixBlock R D F s 0 h) = 0 := by
  have hd := dgCoherentBarPrefixBlock_d R D F s 0 h
  let L := moduleHomShiftBlockLinear R D (n : ℤ) ((n - 1 : ℕ) : ℤ)
    (dgCoherentBarSource R D F ⟨n, s⟩)
    (dgCoherentBarSource R D F (dgCoherentBarTail s 1 h)) 1 2 (by omega)
  have hb := (congrArg L (dgCoherentBarPrefixBoundary_edge R D F s h)).trans L.map_zero
  exact hd.trans ((congrArg (fun z => (-((n - 1 : ℕ) : ℤ)).negOnePow • z) hb).trans
    (smul_zero _))

lemma dgCoherentBarBoundaryTerm_vertex_of_closed {M : ModuleCategory R D}
    (s : I _⦋0⦌)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))).X 1)
    (hf : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))).d 1 2 f = 0) :
    dgCoherentBarBoundaryTerm R D F ⟨0, s⟩ f = 0 := by
  have hz := DGNerve.zero_compose (A := R) (D := RightModule R D)
    (x := ForgetEnrichment.to (Complex R) M)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨0, s⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    f (show (1 : ℤ) + 1 = 2 from rfl)
  simpa only [dgCoherentBarBoundaryTerm, dgCoherentBarColumn, hf, map_zero, zero_add] using hz

lemma dgCoherentBarColumn_maurerCartan_one (s : I _⦋1⦌) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarColumn R D F ⟨1, s⟩) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨1, s⟩))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarColumn R D F ⟨1, s⟩)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  rw [dgCoherentBarColumn_positive_boundary R D F s]
  apply Finset.sum_eq_zero
  intro j _
  cases j with
  | inl i =>
    fin_cases i
    have hz := dgCoherentBarBoundaryTerm_vertex_of_closed R D F
      (M := dgCoherentBarFamily R D F ⟨1, s⟩) (I.δ (1 : Fin 2) s)
      (dgCoherentBarFaceBlock R D F s 0) (dgCoherentBarFaceBlock_d R D F s 0)
    change _ • dgCoherentBarBoundaryTerm R D F _ (dgCoherentBarFaceBlock R D F s 0) = 0
    exact (congrArg (fun z => dgCoherentBarPositiveSign 0 (Sum.inl (0 : Fin 1)) • z) hz).trans
      (smul_zero _)
  | inr k =>
    fin_cases k
    let h : 1 ≤ (1 : ℕ) := le_rfl
    let t : I _⦋0⦌ := (dgCoherentBarTail s 1 h).2
    have hz := dgCoherentBarBoundaryTerm_vertex_of_closed R D F
      (M := dgCoherentBarFamily R D F ⟨1, s⟩) t
      (dgCoherentBarPrefixBlock R D F s 0 h) (dgCoherentBarPrefixBlock_edge_d R D F s h)
    change _ • dgCoherentBarBoundaryTerm R D F _ (dgCoherentBarPrefixBlock R D F s 0 h) = 0
    exact (congrArg (fun z => dgCoherentBarPositiveSign 0 (Sum.inr (0 : Fin 1)) • z) hz).trans
      (smul_zero _)

end SerrePositivity.InfinityCategories
