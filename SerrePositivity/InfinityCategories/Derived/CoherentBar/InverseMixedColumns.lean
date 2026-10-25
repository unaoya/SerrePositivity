module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterCoefficients
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinMixedEndpoints
/-!
概要：任意の pinched 線形単体と native 列から、逆比較の全混合列を作る。
方針：次数符号を戻したパラメーター係数を、元の全単体の実 native 列に後合成する。
規約：実 dg Hom の全次数を保持し、逆構成の HA 方程式は後続で検証する。
使われ方：全写像空間比較の逆射の混合成分。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarInverseMixedColumn {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (s : dgCoherentBarIndex I) :
    GradedHom R (dgCoherentBarSource R D F s) N (q - (s.1 : ℤ)) :=
  compose R (x := dgCoherentBarSource R D F s)
    (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
    (dgCoherentBarInverseParameterCoefficient f L q hL hq)
    (dgCoherentBarNativeColumn R D F hMC s) (by omega)

lemma dgCoherentBarInverseMixedColumn_source_degenerate {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (s : dgCoherentBarDegenerateIndex I) :
    dgCoherentBarInverseMixedColumn R D F hMC N f L q hL hq s.val = 0 := by
  unfold dgCoherentBarInverseMixedColumn
  rw [dgCoherentBarNativeColumn_degenerate R D F hMC s, DGNerve.compose_zero]

lemma dgCoherentBarInverseMixedColumn_differential {m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (L : Finset (Fin (m + 1))) (q : ℤ) (hL : L.Nonempty)
    (hq : q = 1 - (L.card : ℤ)) (s : dgCoherentBarIndex I) :
    differential R (dgCoherentBarInverseMixedColumn R D F hMC N f L q hL hq s) =
      compose R (x := dgCoherentBarSource R D F s)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
        (differential R (dgCoherentBarInverseParameterCoefficient f L q hL hq))
        (dgCoherentBarNativeColumn R D F hMC s)
        (show -(s.1 : ℤ) + (q + 1) = q - (s.1 : ℤ) + 1 by omega) +
      q.negOnePow • compose R (x := dgCoherentBarSource R D F s)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := N)
        (dgCoherentBarInverseParameterCoefficient f L q hL hq)
        (differential R (dgCoherentBarNativeColumn R D F hMC s))
        (show (-(s.1 : ℤ) + 1) + q = q - (s.1 : ℤ) + 1 by omega) := by
  unfold dgCoherentBarInverseMixedColumn
  rw [differential_compose]

end SerrePositivity.InfinityCategories
