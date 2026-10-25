module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeFamilyDegeneracies
/-!
概要：回収した高次 Hom は全単体の混合成分を復元し、その微分は Leibniz 則で比較できる。
方針：非退化の成分同値と退化消滅を合わせ、実加群 Hom の微分公式を適用する。
規約：HA の面方程式との同定は後続で行い、成分比較だけで普遍性を結論しない。
使われ方：余錐族の HA 方程式を写像空間の線形微分方程式へ移す。
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
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyHom_columns {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarIndex I) :
    compose R (x := dgCoherentBarSource R D F s)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgNerve.vertexEquiv R (RightModule R D) y)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c)
      (dgCoherentBarNativeColumn R D F hMC s)
      (show -(s.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.1 : ℤ) by omega) =
      dgCoherentBarCoconeFamilyColumn R D F y c s := by
  classical
  by_cases hs : s.2 ∈ I.nonDegenerate s.1
  · exact dgCoherentBarCoconeFamilyHom_nondegenerate R D F hMC y c ⟨s, hs⟩
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hs
    rw [dgCoherentBarNativeColumn_degenerate R D F hMC ⟨s, hd⟩, DGNerve.compose_zero,
      dgCoherentBarCoconeFamilyColumn_degenerate R D F y c ⟨s, hd⟩]

lemma dgCoherentBarCoconeFamilyHom_differential_columns {m : ℕ}
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarIndex I) :
    differential R (dgCoherentBarCoconeFamilyColumn R D F y c s) =
      compose R (x := dgCoherentBarSource R D F s)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgNerve.vertexEquiv R (RightModule R D) y)
        (differential R (dgCoherentBarCoconeFamilyHom R D F hMC y c))
        (dgCoherentBarNativeColumn R D F hMC s)
        (show -(s.1 : ℤ) + (-(m : ℤ) + 1) = -(m : ℤ) - (s.1 : ℤ) + 1 by omega) +
      (-(m : ℤ)).negOnePow •
        compose R (x := dgCoherentBarSource R D F s)
          (y := dgCoherentBarNormalizedModule R D F hMC)
          (z := dgNerve.vertexEquiv R (RightModule R D) y)
          (dgCoherentBarCoconeFamilyHom R D F hMC y c)
          (differential R (dgCoherentBarNativeColumn R D F hMC s))
          (show (-(s.1 : ℤ) + 1) + -(m : ℤ) = -(m : ℤ) - (s.1 : ℤ) + 1 by omega) := by
  rw [← dgCoherentBarCoconeFamilyHom_columns R D F hMC y c s, differential_compose]

end SerrePositivity.InfinityCategories
