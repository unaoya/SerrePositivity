module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentLayerAnnihilation

/-!
概要：各実 theta 列を直下一次元層へ射影すると一次列と一致する。
方針：高次 HA 項の二段下降を次数付き元へ適用する。
規約：高次項を図式から除かず、指定した層への射影での消滅を示す。
使われ方：連結射の代表元公式と通常の bar 微分の比較。
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

lemma dgCoherentBarSupportedHom_layer_zero (M : ModuleCategory R D) (r : ℤ)
    {m n : ℕ} (hmn : m < n)
    (z : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G))).X r)
    (hz : z ∈ dgCoherentBarHomFiltration R D G M r m)
    (x : D) (q : ℤ) (a : (moduleDegreeEvaluation R D x q).obj M) :
    (moduleDegreeEvaluation R D x (q + r)).map
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
        ((((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f r z).v
            q (q + r) rfl) a) = 0 := by
  rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  apply dgCoherentBarLayerProjection_annihilate R D G x (q + r) hmn
  exact Submodule.mem_map.mpr
    ⟨_, dgCoherentBarHomFiltration_apply R D G M r m z hz x q a, rfl⟩

lemma dgCoherentBarHigherColumn_projected_zero {n : ℕ} (s : I _⦋n + 1⦌)
    (x : D) (q : ℤ) (a : (moduleDegreeEvaluation R D x q).obj
      (dgCoherentBarFamily R D G ⟨n + 1, s⟩)) :
    (moduleDegreeEvaluation R D x (q + 1)).map
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
        ((((moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
            (dgCoherentBarHigherColumn R D G s)).v q (q + 1) rfl) a) = 0 := by
  cases n with
  | zero =>
    simp only [dgCoherentBarHigherColumn, Fin.sum_univ_zero, smul_zero, map_zero,
      Cochain.zero_v]
    change (moduleDegreeEvaluation R D x (q + 1)).map
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G 0) 0 = 0
    exact map_zero _
  | succ n =>
    exact dgCoherentBarSupportedHom_layer_zero R D G _ 1 (by omega)
      (dgCoherentBarHigherColumn R D G s) (dgCoherentBarHigherColumn_mem_filtration R D G s)
        x q a

lemma dgCoherentBarColumn_projected_first {n : ℕ} (s : I _⦋n + 1⦌)
    (x : D) (q : ℤ) (a : (moduleDegreeEvaluation R D x q).obj
      (dgCoherentBarFamily R D G ⟨n + 1, s⟩)) :
    (moduleDegreeEvaluation R D x (q + 1)).map
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
        ((((moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
            (dgCoherentBarColumn R D G ⟨n + 1, s⟩)).v q (q + 1) rfl) a) =
    (moduleDegreeEvaluation R D x (q + 1)).map
      (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
        ((((moduleHomπ R D
          (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
          (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
            (dgCoherentBarFirstColumn R D G s)).v q (q + 1) rfl) a) := by
  rw [dgCoherentBarColumn_eq_first_add_higher]
  simp only [map_add]
  erw [Cochain.add_v]
  let p := (moduleDegreeEvaluation R D x (q + 1)).map
    (dgCoherentBarNormalizedProjection R D G ≫ dgCoherentBarLayerProjection R D G n)
  let f := (((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
      (dgCoherentBarFirstColumn R D G s)).v q (q + 1) rfl)
  let g := (((moduleHomπ R D
    (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D G ⟨n + 1, s⟩))
    (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D G)) x).f 1
      (dgCoherentBarHigherColumn R D G s)).v q (q + 1) rfl)
  change p ((f + g) a) = p (f a)
  have hadd : (f + g) a = f a + g a := rfl
  rw [hadd, map_add, dgCoherentBarHigherColumn_projected_zero R D G s x q a, add_zero]

end SerrePositivity.InfinityCategories
