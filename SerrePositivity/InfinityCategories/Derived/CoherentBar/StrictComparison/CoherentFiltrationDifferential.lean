module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFiltration

/-!
概要：内部微分は単体次元を保ち、実 coherent theta は一段以上下げる。
方針：像部分加群の上限での帰納と、正規化射影との可換式を用いる。
規約：元の HA 全成分と実 normalized theta を使う。
使われ方：正規化 bar の単体次元フィルトレーションの微分。
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
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarHomFiltration_d (M : ModuleCategory R D) (q : ℤ) (n : ℕ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).X q)
    (hz : z ∈ dgCoherentBarHomFiltration R D G M q n) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).d q (q + 1) z ∈
      dgCoherentBarHomFiltration R D G M (q + 1) n := by
  refine Submodule.iSup_induction
    (motive := fun z => (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).d q (q + 1) z ∈
        dgCoherentBarHomFiltration R D G M (q + 1) n)
    (fun s : {s : dgCoherentBarIndex I // s.1 ≤ n} =>
      LinearMap.range ((eHomWhiskerLeft (Complex R) M
        (Sigma.ι (dgCoherentBarFamily R D G) s.val)).f q).hom) hz ?_ ?_ ?_
  · intro s z hz
    obtain ⟨a, rfl⟩ := hz
    erw [dgStrictHom_postcompose_d R D]
    exact dgCoherentBarHomFiltration_inclusion R D G M (q + 1) n s.val s.property _
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb

lemma dgCoherentBarNormalizedHomFiltration_d (M : ModuleCategory R D) (q : ℤ) (n : ℕ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))).X q)
    (hz : z ∈ dgCoherentBarNormalizedHomFiltration R D G M q n) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))).d q (q + 1) z ∈
      dgCoherentBarNormalizedHomFiltration R D G M (q + 1) n := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  erw [dgStrictHom_postcompose_d R D]
  exact Submodule.mem_map.mpr ⟨_, dgCoherentBarHomFiltration_d R D G M q n a ha, rfl⟩

lemma dgCoherentBarNormalizedHomFiltration_theta (M : ModuleCategory R D) (q : ℤ) (n : ℕ)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))).X q)
    (hz : z ∈ dgCoherentBarNormalizedHomFiltration R D G M q n) :
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))
      (dgCoherentBarNormalizedTheta R D G) z (show q + 1 = q + 1 from rfl) ∈
      dgCoherentBarNormalizedHomFiltration R D G M (q + 1) (n - 1) := by
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
  erw [moduleHomClosedInsertion R D, dgCoherentBarNormalizedTheta_projection,
    ← dgCoherentBarHom_postcompose_comp R D]
  apply Submodule.mem_map.mpr
  refine ⟨_, ?_, rfl⟩
  apply dgCoherentBarHomFiltration_postcompose R D G a (dgCoherentBarTheta R D G) ha
  intro s hs
  rw [dgCoherentBarTheta_restrict]
  exact dgCoherentBarHomFiltration_mono R D G (dgCoherentBarFamily R D G s) 1
    (Nat.sub_le_sub_right hs 1) (dgCoherentBarColumn_mem_filtration R D G s)

end SerrePositivity.InfinityCategories
