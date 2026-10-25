module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FiltrationColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedHomFactorization
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NormalizedDifferential
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.HomExchange

/-!
概要：元の coherent bar の単体次元による支持を正規化側へ移す。
方針：元の全 HA 項の支持上限を、同じ正規化射影で送る。
規約：G の高次 prefix 係数を消さず、落ちる単体次元を数える。
使われ方：単体次元フィルトレーションの微分とその次数一成分。
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

def dgCoherentBarNormalizedHomFiltration (M : ModuleCategory R D) (q : ℤ) (n : ℕ) :
    Submodule R ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarNormalizedGraded R D G))).X q) :=
  (dgCoherentBarHomFiltration R D G M q n).map
    ((eHomWhiskerLeft (Complex R) M (dgCoherentBarNormalizedProjection R D G)).f q).hom

lemma dgCoherentBarNormalizedHomFiltration_mono (M : ModuleCategory R D) (q : ℤ)
    {n m : ℕ} (h : n ≤ m) :
    dgCoherentBarNormalizedHomFiltration R D G M q n ≤
      dgCoherentBarNormalizedHomFiltration R D G M q m :=
  Submodule.map_mono (dgCoherentBarHomFiltration_mono R D G M q h)

lemma dgCoherentBarNormalizedTheta_restrict (s : dgCoherentBarNormalizedIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s)
      (dgCoherentBarNormalizedGraded R D G)).f 1 (dgCoherentBarNormalizedTheta R D G) =
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D G s.val)
      (dgCoherentBarNormalizedProjection R D G)).f 1 (dgCoherentBarColumn R D G s.val) := by
  unfold dgCoherentBarNormalizedTheta
  rw [dgCoherentBarHom_precompose_comp R D, dgCoherentBarNormalizedInclusion_ι,
    dgStrictHom_whisker_exchange R D, dgCoherentBarTheta_restrict]

lemma dgCoherentBarNormalizedTheta_restrict_mem_filtration
    (s : dgCoherentBarNormalizedIndex I) :
    (eHomWhiskerRight (Complex R) (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s)
      (dgCoherentBarNormalizedGraded R D G)).f 1 (dgCoherentBarNormalizedTheta R D G) ∈
    dgCoherentBarNormalizedHomFiltration R D G (dgCoherentBarFamily R D G s.val)
      1 (s.val.1 - 1) := by
  rw [dgCoherentBarNormalizedTheta_restrict]
  exact Submodule.mem_map.mpr
    ⟨_, dgCoherentBarColumn_mem_filtration R D G s.val, rfl⟩

/-- k 次の HA 係数は単体次元をちょうど k+1 下げる。 -/
lemma dgCoherentBarPrefixColumn_mem_filtration {n : ℕ} (s : I _⦋n⦌)
    (k : ℕ) (hk : k + 1 ≤ n) :
    dgCoherentBarPrefixColumn R D G s k hk ∈
      dgCoherentBarHomFiltration R D G (dgCoherentBarFamily R D G ⟨n, s⟩) 1
        (n - (k + 1)) :=
  dgCoherentBarHomFiltration_inclusion R D G (dgCoherentBarFamily R D G ⟨n, s⟩)
    1 (n - (k + 1)) (dgCoherentBarTail s (k + 1) hk) le_rfl _

/-- 高次 HA 係数は単体次元を二つ以上下げ、一次成分には現れない。 -/
lemma dgCoherentBarHigherPrefixColumn_mem_filtration {n : ℕ} (s : I _⦋n⦌)
    (k : ℕ) (hk : k + 1 ≤ n) (hkpos : 0 < k) :
    dgCoherentBarPrefixColumn R D G s k hk ∈
      dgCoherentBarHomFiltration R D G (dgCoherentBarFamily R D G ⟨n, s⟩) 1 (n - 2) :=
  dgCoherentBarHomFiltration_mono R D G (dgCoherentBarFamily R D G ⟨n, s⟩) 1
    (by omega) (dgCoherentBarPrefixColumn_mem_filtration R D G s k hk)

end SerrePositivity.InfinityCategories
