module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentDiagramEdgeBoundary
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarFaceDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarPrefixDifferential
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarBoundaryTerms
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

lemma dgCoherentBarPrefixBoundary_edge {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBoundary R D F s 0 h = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBoundary
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTopBoundary_edge, map_zero]

lemma dgCoherentBarPrefixBlock_edge_d {n : ℕ} (s : I _⦋n⦌) (h : 1 ≤ n) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 h)))).d 1 2
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s 0 h) = 0 := by
  have hd := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock_d R D F s 0 h
  let L := _root_.SerrePositivity.DifferentialGraded.moduleHomShiftBlockLinear R D (n : ℤ) ((n - 1 : ℕ) : ℤ)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 h)) 1 2 (by omega)
  have hb := (congrArg L (dgCoherentBarPrefixBoundary_edge R D F s h)).trans L.map_zero
  exact hd.trans ((congrArg (fun z => (-((n - 1 : ℕ) : ℤ)).negOnePow • z) hb).trans
    (smul_zero _))

lemma dgCoherentBarBoundaryTerm_vertex_of_closed {M : _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D}
    (s : I _⦋0⦌)
    (f : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨0, s⟩))).X 1)
    (hf : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨0, s⟩))).d 1 2 f = 0) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBoundaryTerm R D F ⟨0, s⟩ f = 0 := by
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose (A := R) (D := RightModule R D)
    (x := ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R) M)
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨0, s⟩))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    f (show (1 : ℤ) + 1 = 2 from rfl)
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBoundaryTerm, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn, hf, map_zero, zero_add] using hz

lemma dgCoherentBarColumn_maurerCartan_one (s : I _⦋1⦌) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨1, s⟩))
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))).d 1 2
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨1, s⟩) +
      compose R (x := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨1, s⟩))
        (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn R D F ⟨1, s⟩)
        (show (1 : ℤ) + 1 = 2 from rfl) = 0 := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarColumn_positive_boundary R D F s]
  apply Finset.sum_eq_zero
  intro j _
  cases j with
  | inl i =>
    fin_cases i
    have hz := dgCoherentBarBoundaryTerm_vertex_of_closed R D F
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨1, s⟩) (I.δ (1 : Fin 2) s)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s 0) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock_d R D F s 0)
    change _ • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBoundaryTerm R D F _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceBlock R D F s 0) = 0
    exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveSign 0 (Sum.inl (0 : Fin 1)) • z) hz).trans
      (smul_zero _)
  | inr k =>
    fin_cases k
    let h : 1 ≤ (1 : ℕ) := le_rfl
    let t : I _⦋0⦌ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail s 1 h).2
    have hz := dgCoherentBarBoundaryTerm_vertex_of_closed R D F
      (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨1, s⟩) t
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s 0 h) (dgCoherentBarPrefixBlock_edge_d R D F s h)
    change _ • _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBoundaryTerm R D F _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixBlock R D F s 0 h) = 0
    exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPositiveSign 0 (Sum.inr (0 : Fin 1)) • z) hz).trans
      (smul_zero _)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
