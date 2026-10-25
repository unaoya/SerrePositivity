module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftDegeneracies
/-!
概要：持ち上げ余錐について、回収した高次 Hom は全単体の混合成分を復元し、その微分は Leibniz 則で比較できる。
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

lemma dgCoherentBarCoconeLiftHom_columns {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarIndex I) :
    compose R (x := dgCoherentBarSource R D F s)
      (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgCoherentBarCoconeLiftTarget R D F c)
      (dgCoherentBarCoconeLiftHom R D F hMC c)
      (dgCoherentBarNativeColumn R D F hMC s)
      (show -(s.1 : ℤ) + -(m : ℤ) = -(m : ℤ) - (s.1 : ℤ) by omega) =
      dgCoherentBarCoconeLiftColumn R D F c s := by
  classical
  by_cases hs : s.2 ∈ I.nonDegenerate s.1
  · exact dgCoherentBarCoconeLiftHom_nondegenerate R D F hMC c ⟨s, hs⟩
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hs
    rw [dgCoherentBarNativeColumn_degenerate R D F hMC ⟨s, hd⟩, DGNerve.compose_zero,
      dgCoherentBarCoconeLiftColumn_degenerate R D F c ⟨s, hd⟩]

lemma dgCoherentBarCoconeLiftHom_differential_columns {m : ℕ}
    (c : (sliceUnder F) _⦋m⦌) (s : dgCoherentBarIndex I) :
    differential R (dgCoherentBarCoconeLiftColumn R D F c s) =
      compose R (x := dgCoherentBarSource R D F s)
        (y := dgCoherentBarNormalizedModule R D F hMC)
        (z := dgCoherentBarCoconeLiftTarget R D F c)
        (differential R (dgCoherentBarCoconeLiftHom R D F hMC c))
        (dgCoherentBarNativeColumn R D F hMC s)
        (show -(s.1 : ℤ) + (-(m : ℤ) + 1) = -(m : ℤ) - (s.1 : ℤ) + 1 by omega) +
      (-(m : ℤ)).negOnePow •
        compose R (x := dgCoherentBarSource R D F s)
          (y := dgCoherentBarNormalizedModule R D F hMC)
          (z := dgCoherentBarCoconeLiftTarget R D F c)
          (dgCoherentBarCoconeLiftHom R D F hMC c)
          (differential R (dgCoherentBarNativeColumn R D F hMC s))
          (show (-(s.1 : ℤ) + 1) + -(m : ℤ) = -(m : ℤ) - (s.1 : ℤ) + 1 by omega) := by
  rw [← dgCoherentBarCoconeLiftHom_columns R D F hMC c s, differential_compose]

end SerrePositivity.InfinityCategories
