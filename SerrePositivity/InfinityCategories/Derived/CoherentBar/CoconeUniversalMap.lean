module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomRestoration
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeFullCoefficient
public import SerrePositivity.DifferentialGraded.Module.HomCycles
/-!
概要：任意の native 余錐から回収した Hom 候補は閉じ、同じ正規化実 bar からの実加群射を与える。
方針：回収単体の HA 方程式で微分の全 native 列を消し、全次数 Hom の単射性で判定する。
規約：単なる評価ごとの射ではなく、全 dg 自然な閉零要素を使う。
使われ方：native Hom 普遍性の逆射の零次元部分。
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
  (hMC : dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeHomCandidate_d_column (c : JoinCocone F)
    (s : dgCoherentBarIndex I) :
    compose R (x := dgCoherentBarSource R D F s)
      (y := dgCoherentBarNormalizedModule R D F hMC) (z := dgCoherentBarCoconeModule R D F c)
      ((moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
        (dgCoherentBarCoconeModule R D F c)).d 0 1 (dgCoherentBarCoconeHomCandidate R D F hMC c))
      (dgCoherentBarNativeColumn R D F hMC s)
      (show -(s.1 : ℤ) + 1 = 1 - (s.1 : ℤ) by omega) = 0 := by
  rcases s with ⟨n, s⟩
  have heq := dgCoherentBarCoconeRestoredData_eq R D F hMC c s
  have hHA : differential R ((dgCoherentBarCoconeRestoredData R D F hMC c s).hom
      Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega)) =
      (dgCoherentBarCoconeRestoredData R D F hMC c s).rhs
        Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
        (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega) := by
    rw [heq]
    exact (dgCoherentBarCoconeSimplex R D F c s).equation _ _ _ _ _ _ _ _
  have hz := dgCoherentBarPostLastData_residual (dgCoherentBarNativeSimplex R D F hMC s)
    (dgCoherentBarCoconeModule R D F c) (dgCoherentBarCoconeCandidateAt R D F hMC c s)
    Finset.univ 0 (-(n : ℤ)) (coherentDiagramTop_card n) (coherentDiagramTop_min n)
    (coherentDiagramTop_max n) (by simp) hHA
  have hx := dgCoherentBarNativeSimplex_source R D F hMC s
  have hy := dgCoherentBarNativeSimplex_last R D F hMC s
  have hd := gradedHom_differential_heq (A := R) (D := RightModule R D) hy rfl rfl _ _
    (dgCoherentBarCoconeCandidateAt_heq R D F hMC c s)
  have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy rfl rfl rfl (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega)
    (differential R (dgCoherentBarCoconeCandidateAt R D F hMC c s))
    ((dgCoherentBarNativeSimplex R D F hMC s).hom
      Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ)) (coherentDiagramTop_card n)
      (coherentDiagramTop_min n) (coherentDiagramTop_max n) (by simp; omega))
    ((moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeModule R D F c)).d 0 1 (dgCoherentBarCoconeHomCandidate R D F hMC c))
    (dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
    hd (dgCoherentBarNativeSimplex_full_hom_heq R D F hMC s) rfl (by omega)
  rw [hz] at hc
  have hzero := gradedHom_zero_heq (A := R) (D := RightModule R D)
    (y := dgCoherentBarCoconeModule R D F c) hx rfl
    (show -(n : ℤ) + 1 = 1 - (n : ℤ) by omega)
  exact (eq_of_heq (hzero.symm.trans hc)).symm

lemma dgCoherentBarCoconeHomCandidate_closed (c : JoinCocone F) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeModule R D F c)).d 0 1
      (dgCoherentBarCoconeHomCandidate R D F hMC c) = 0 := by
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC
    (dgCoherentBarCoconeModule R D F c) 1).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates]
  simpa only [map_zero, Pi.zero_apply] using
    dgCoherentBarCoconeHomCandidate_d_column R D F hMC c s.val

def dgCoherentBarCoconeUniversalMap (c : JoinCocone F) :
    ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC) ⟶
      ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D F c) :=
  moduleMorphismOfCycle R D
    (M := ForgetEnrichment.of (Complex R) (dgCoherentBarNormalizedModule R D F hMC))
    (N := ForgetEnrichment.of (Complex R) (dgCoherentBarCoconeModule R D F c))
    (dgCoherentBarCoconeHomCandidate R D F hMC c)
    (dgCoherentBarCoconeHomCandidate_closed R D F hMC c)

lemma dgCoherentBarCoconeUniversalMap_cycle (c : JoinCocone F) :
    (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R)
      (dgCoherentBarCoconeUniversalMap R D F hMC c))).val =
      dgCoherentBarCoconeHomCandidate R D F hMC c :=
  moduleMorphismOfCycle_cycle R D _ _

end SerrePositivity.InfinityCategories
