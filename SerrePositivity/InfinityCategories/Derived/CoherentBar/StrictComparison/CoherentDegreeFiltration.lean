module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiltrationDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiniteSupport

/-!
概要：評価複体の元に対する単体次元フィルトレーション。
方針：各 summand の次数評価の像を取り、Hom の支持条件を元の支持条件へ送る。
規約：実余積の元を用い、coherent 図式の strict 化は要求しない。
使われ方：内部微分・摂動微分の支持と、有限 support による収束。
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

def dgCoherentBarDegreeFiltration (x : D) (q : ℤ) (n : ℕ) :
    Submodule R ((moduleDegreeEvaluation R D x q).obj (dgCoherentBarGraded R D G)) :=
  ⨆ s : {s : dgCoherentBarIndex I // s.1 ≤ n},
    LinearMap.range ((moduleDegreeEvaluation R D x q).map
      (Sigma.ι (dgCoherentBarFamily R D G) s.val)).hom

def dgCoherentBarNormalizedDegreeFiltration (x : D) (q : ℤ) (n : ℕ) :
    Submodule R ((moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G)) :=
  (dgCoherentBarDegreeFiltration R D G x q n).map
    ((moduleDegreeEvaluation R D x q).map (dgCoherentBarNormalizedProjection R D G)).hom

lemma dgCoherentBarDegreeFiltration_inclusion (x : D) (q : ℤ) (n : ℕ)
    (s : dgCoherentBarIndex I) (hs : s.1 ≤ n)
    (a : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarFamily R D G s)) :
    (moduleDegreeEvaluation R D x q).map (Sigma.ι (dgCoherentBarFamily R D G) s) a ∈
      dgCoherentBarDegreeFiltration R D G x q n :=
  Submodule.mem_iSup_of_mem (i := (⟨s, hs⟩ : {s : dgCoherentBarIndex I // s.1 ≤ n}))
    ⟨a, rfl⟩

lemma dgCoherentBarDegreeFiltration_mono (x : D) (q : ℤ) {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarDegreeFiltration R D G x q n ≤ dgCoherentBarDegreeFiltration R D G x q m := by
  apply iSup_le
  intro s
  rintro _ ⟨a, rfl⟩
  exact dgCoherentBarDegreeFiltration_inclusion R D G x q m s.val (s.property.trans h) a

lemma dgCoherentBarNormalizedDegreeFiltration_mono (x : D) (q : ℤ) {n m : ℕ}
    (h : n ≤ m) :
    dgCoherentBarNormalizedDegreeFiltration R D G x q n ≤
      dgCoherentBarNormalizedDegreeFiltration R D G x q m :=
  Submodule.map_mono (dgCoherentBarDegreeFiltration_mono R D G x q h)

lemma dgCoherentBarHomFiltration_apply (M : ModuleCategory R D) (r : ℤ) (n : ℕ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).X r)
    (hz : z ∈ dgCoherentBarHomFiltration R D G M r n) (x : D) (p : ℤ)
    (a : (moduleDegreeEvaluation R D x p).obj M) :
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f r z).v
        p (p + r) rfl) a ∈ dgCoherentBarDegreeFiltration R D G x (p + r) n := by
  refine Submodule.iSup_induction
    (motive := fun z => (((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f r z).v
        p (p + r) rfl) a ∈ dgCoherentBarDegreeFiltration R D G x (p + r) n)
    (fun s : {s : dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (Complex R) M
        (Sigma.ι (dgCoherentBarFamily R D G) s.val)).f r).hom) hz ?_ ?_ ?_
  · intro s z hz
    obtain ⟨b, rfl⟩ := hz
    erw [moduleHomWhiskerLeft_apply_π, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    exact dgCoherentBarDegreeFiltration_inclusion R D G x (p + r) n s.val s.property _
  · simp only [map_zero, Cochain.zero_v]
    exact Submodule.zero_mem _
  · intro a' b' ha hb
    simp only [map_add, Cochain.add_v]
    exact Submodule.add_mem _ ha hb

lemma dgCoherentBarNormalizedDegreeFiltration_inclusion (x : D) (q : ℤ) (n : ℕ)
    (s : dgCoherentBarNormalizedIndex I) (hs : s.val.1 ≤ n)
    (a : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedFamily R D G s)) :
    (moduleDegreeEvaluation R D x q).map (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s) a ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  apply Submodule.mem_map.mpr
  refine ⟨_, dgCoherentBarDegreeFiltration_inclusion R D G x q n s.val hs a, ?_⟩
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, dgCoherentBarNormalizedProjection_ι]

lemma dgCoherentBarNormalizedDegreeFiltration_exhaustive (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G)) :
    ∃ n, z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n := by
  classical
  obtain ⟨n, t, a, hn, ha⟩ := dgCoherentBarNormalizedDegree_boundedSupport R D G x q z
  refine ⟨n, ?_⟩
  rw [← ha]
  exact Submodule.sum_mem _ (fun s hs =>
    dgCoherentBarNormalizedDegreeFiltration_inclusion R D G x q n s (hn s hs) (a s))

end SerrePositivity.InfinityCategories
