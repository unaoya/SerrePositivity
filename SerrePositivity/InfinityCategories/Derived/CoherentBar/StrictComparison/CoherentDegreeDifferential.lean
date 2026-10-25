module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentDegreeFiltration
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Unconditional
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomDegrees

/-!
概要：元の実正規化 bar の微分が単体次元フィルトレーションを保つ。
方針：評価で内部微分と theta の作用を分け、theta の支持を各列から判定する。
規約：G は元の coherent 図式。高次 HA 項を含む実微分を使う。
使われ方：ホモロジー比較の単体次元による有限帰納。
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

lemma dgCoherentBarHomogeneous_pre_apply {M N P : ModuleCategory R D}
    (f : M ⟶ N) (r : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X r) (x : D) (p : ℤ)
    (a : (moduleDegreeEvaluation R D x p).obj M) :
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P) x).f r z).v p (p + r) rfl)
        ((moduleDegreeEvaluation R D x p).map f a) =
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P) x).f r
        ((eHomWhiskerRight (Complex R) f P).f r z)).v p (p + r) rfl) a := by
  erw [moduleHomWhiskerRight_apply_π, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  rfl

lemma dgCoherentBarHomogeneous_post_apply {M N P : ModuleCategory R D}
    (f : N ⟶ P) (r : ℤ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X r) (x : D) (p : ℤ)
    (a : (moduleDegreeEvaluation R D x p).obj M) :
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P) x).f r
        ((eHomWhiskerLeft (Complex R) M f).f r z)).v p (p + r) rfl) a =
    (moduleDegreeEvaluation R D x (p + r)).map f
      ((((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) N) x).f r z).v p (p + r) rfl) a) := by
  erw [moduleHomWhiskerLeft_apply_π, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rfl

variable {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

set_option maxHeartbeats 800000 in
-- 実 coproduct と Hom end の次数評価の照合に限った局所上限。
lemma dgCoherentBarDegreeFiltration_theta (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarGraded R D G))
    (hz : z ∈ dgCoherentBarDegreeFiltration R D G x q n) :
    (((moduleHomπ R D (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
        (dgCoherentBarTheta R D G)).v q (q + 1) rfl) z ∈
      dgCoherentBarDegreeFiltration R D G x (q + 1) (n - 1) := by
  refine Submodule.iSup_induction
    (motive := fun z => (((moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
        (dgCoherentBarTheta R D G)).v q (q + 1) rfl) z ∈
      dgCoherentBarDegreeFiltration R D G x (q + 1) (n - 1))
    (fun s : {s : dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarFamily R D G) s.val)).hom) hz ?_ ?_ ?_
  · intro s a ha
    obtain ⟨b, rfl⟩ := ha
    erw [dgCoherentBarHomogeneous_pre_apply R D
      (Sigma.ι (dgCoherentBarFamily R D G) s.val) 1 (dgCoherentBarTheta R D G) x q b,
      dgCoherentBarTheta_restrict R D G s.val]
    exact dgCoherentBarHomFiltration_apply R D G _ 1 (n - 1) _
      (dgCoherentBarHomFiltration_mono R D G _ 1 (Nat.sub_le_sub_right s.property 1)
        (dgCoherentBarColumn_mem_filtration R D G s.val)) x q b
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

set_option maxHeartbeats 800000 in
-- 正規化射影を介した同じ Hom end の評価に限った局所上限。
lemma dgCoherentBarNormalizedDegreeFiltration_theta (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    (((moduleHomπ R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G)) x).f 1
        (dgCoherentBarNormalizedTheta R D G)).v q (q + 1) rfl) z ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) (n - 1) := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  erw [dgCoherentBarHomogeneous_pre_apply R D
      (dgCoherentBarNormalizedProjection R D G) 1 (dgCoherentBarNormalizedTheta R D G) x q a,
    dgCoherentBarNormalizedTheta_projection R D G,
    dgCoherentBarHomogeneous_post_apply R D]
  exact Submodule.mem_map.mpr
    ⟨_, dgCoherentBarDegreeFiltration_theta R D G x q n a ha, rfl⟩

lemma dgCoherentBarDegreeFiltration_internal_d (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarGraded R D G))
    (hz : z ∈ dgCoherentBarDegreeFiltration R D G x q n) :
    ((moduleEvaluation R D x).obj (dgCoherentBarGraded R D G)).d q (q + 1) z ∈
      dgCoherentBarDegreeFiltration R D G x (q + 1) n := by
  refine Submodule.iSup_induction
    (motive := fun z => ((moduleEvaluation R D x).obj
      (dgCoherentBarGraded R D G)).d q (q + 1) z ∈
        dgCoherentBarDegreeFiltration R D G x (q + 1) n)
    (fun s : {s : dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarFamily R D G) s.val)).hom) hz ?_ ?_ ?_
  · intro s a ha
    obtain ⟨b, rfl⟩ := ha
    have h := ConcreteCategory.congr_hom
      (((moduleEvaluation R D x).map
        (Sigma.ι (dgCoherentBarFamily R D G) s.val)).comm q (q + 1)) b
    change ((moduleEvaluation R D x).obj (dgCoherentBarGraded R D G)).d q (q + 1)
      ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarFamily R D G) s.val) b) = _ at h
    erw [h]
    exact dgCoherentBarDegreeFiltration_inclusion R D G x (q + 1) n s.val s.property _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

lemma dgCoherentBarNormalizedDegreeFiltration_internal_d (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d q (q + 1) z ∈
      dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) n := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  have h := ConcreteCategory.congr_hom
    (((moduleEvaluation R D x).map (dgCoherentBarNormalizedProjection R D G)).comm
      q (q + 1)) a
  change ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d
    q (q + 1) ((moduleDegreeEvaluation R D x q).map
      (dgCoherentBarNormalizedProjection R D G) a) = _ at h
  erw [h]
  exact Submodule.mem_map.mpr
    ⟨_, dgCoherentBarDegreeFiltration_internal_d R D G x q n a ha, rfl⟩

lemma dgCoherentBarNormalizedDegreeFiltration_d (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G))
    (hz : z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x q n) :
    ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d
      q (q + 1) z ∈ dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) n := by
  rw [dgCoherentBarNormalizedModule_d]
  change _ + _ ∈ dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) n
  apply Submodule.add_mem
  · exact dgCoherentBarNormalizedDegreeFiltration_internal_d R D G x q n z hz
  · exact dgCoherentBarNormalizedDegreeFiltration_mono R D G x (q + 1)
      (Nat.sub_le n 1) (dgCoherentBarNormalizedDegreeFiltration_theta R D G x q n z hz)

end SerrePositivity.InfinityCategories
