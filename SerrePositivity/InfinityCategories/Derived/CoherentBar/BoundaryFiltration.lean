module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FiltrationColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizationStages
/-!
概要：段階的正規化の境界は元の単体次数を増やさず、段階より低い次数では零になる。
方針：theta と退化作用素の標的支持を合成し、全 Hom の列への制限で判定する。
規約：theta の全 prefix 項を保持し、無限和を使わない。
使われ方：各単体上での有限段階の安定化と、完成した正規化ホモトピー。
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

def dgCoherentBarNormalizationBoundaryGraded (q : ℕ) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 0 :=
  compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarTheta R D F) (dgCoherentBarNormalizationHomotopyGraded R D F q)
    (show (-1 : ℤ) + 1 = 0 from rfl) +
  compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarNormalizationHomotopyGraded R D F q) (dgCoherentBarTheta R D F)
    (show (1 : ℤ) + -1 = 0 from rfl)

lemma dgCoherentBarNormalizationBoundaryGraded_restrict (q : ℕ) (s : dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) =
    compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarNormalizationHomotopyColumn R D F q s)
      (show (-1 : ℤ) + 1 = 0 from rfl) +
    compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarNormalizationHomotopyGraded R D F q) (dgCoherentBarColumn R D F s)
      (show (1 : ℤ) + -1 = 0 from rfl) := by
  rw [dgCoherentBarNormalizationBoundaryGraded, map_add,
    moduleHomRestriction_compose R D, moduleHomRestriction_compose R D,
    dgCoherentBarTheta_restrict, dgCoherentBarNormalizationHomotopyGraded_restrict]

lemma dgCoherentBarNormalizationBoundaryGraded_restrict_eq_zero (q : ℕ)
    (s : dgCoherentBarIndex I) (hs : s.1 < q) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) = 0 := by
  have hz := dgCoherentBarHomFiltration_postcompose_zero R D F
    (dgCoherentBarColumn R D F s) (dgCoherentBarNormalizationHomotopyGraded R D F q)
    (dgCoherentBarColumn_mem_filtration R D F s) (fun t ht => by
      rw [dgCoherentBarNormalizationHomotopyGraded_restrict,
        dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q t (by omega)])
    (show (1 : ℤ) + -1 = 0 from rfl)
  rw [dgCoherentBarNormalizationBoundaryGraded_restrict,
    dgCoherentBarNormalizationHomotopyColumn_eq_zero_of_lt R D F q s hs,
    DGNerve.compose_zero, hz, add_zero]

set_option maxHeartbeats 800000 in
-- 二種類の斉次合成と元の Hom end の支持上限を同時に照合する局所上限。
lemma dgCoherentBarNormalizationBoundaryGraded_mem_filtration (q : ℕ)
    (s : dgCoherentBarIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarFamily R D F) s)
      (dgCoherentBarGraded R D F)).f 0 (dgCoherentBarNormalizationBoundaryGraded R D F q) ∈
      dgCoherentBarHomFiltration R D F (dgCoherentBarFamily R D F s) 0 s.1 := by
  rw [dgCoherentBarNormalizationBoundaryGraded_restrict]
  apply Submodule.add_mem
  · exact dgCoherentBarHomFiltration_postcompose R D F
      (M := dgCoherentBarFamily R D F s) (n := s.1 + 1) (m := s.1)
      (dgCoherentBarNormalizationHomotopyColumn R D F q s) (dgCoherentBarTheta R D F)
      (dgCoherentBarNormalizationHomotopyColumn_mem_filtration R D F q s)
      (fun t ht => by
        rw [dgCoherentBarTheta_restrict]
        exact dgCoherentBarHomFiltration_mono R D F (dgCoherentBarFamily R D F t) 1
          (n := t.1 - 1) (m := s.1) (by omega)
          (dgCoherentBarColumn_mem_filtration R D F t))
      (show (-1 : ℤ) + 1 = 0 from rfl)
  · rcases s with ⟨n, s⟩
    cases n with
    | zero =>
      rw [dgCoherentBarColumn, DGNerve.compose_zero]
      exact Submodule.zero_mem _
    | succ n =>
      simpa only [Nat.succ_eq_add_one] using (dgCoherentBarHomFiltration_postcompose R D F
        (M := dgCoherentBarFamily R D F ⟨n + 1, s⟩) (n := n) (m := n + 1)
        (dgCoherentBarColumn R D F ⟨n + 1, s⟩)
        (dgCoherentBarNormalizationHomotopyGraded R D F q)
        (dgCoherentBarColumn_succ_mem_filtration R D F s)
        (fun t ht => by
          rw [dgCoherentBarNormalizationHomotopyGraded_restrict]
          exact dgCoherentBarHomFiltration_mono R D F (dgCoherentBarFamily R D F t) (-1)
            (n := t.1 + 1) (m := n + 1) (by omega)
            (dgCoherentBarNormalizationHomotopyColumn_mem_filtration R D F q t))
        (show (1 : ℤ) + -1 = 0 from rfl))

end SerrePositivity.InfinityCategories
