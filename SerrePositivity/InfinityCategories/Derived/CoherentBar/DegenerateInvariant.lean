module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PositiveDegenerateColumn
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.ZeroDegenerateColumn
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.DegenerateSplitting
/-!
概要：元の theta の全退化列は、非退化因子への射影で零になる。
方針：Mathlib の退化単体表示を使い、零位置と正位置の係数検証を統合する。
規約：元の dgCoherentBarColumn と dgCoherentBarTheta を使う。MC の証明を変更しない。
使われ方：同じ微分の正規化商と退化部分の縮約。
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

lemma dgCoherentBarColumn_degenerate_normalizedProjection (s : dgCoherentBarDegenerateIndex I) :
    (eHomWhiskerLeft (Complex R) (dgCoherentBarFamily R D F s.val)
      (dgCoherentBarNormalizedProjection R D F)).f 1
      (dgCoherentBarColumn R D F s.val) = 0 := by
  rcases s with ⟨⟨n, s⟩, hs⟩
  cases n with
  | zero => simp only [I.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    rw [I.degenerate_eq_iUnion_range_σ] at hs
    obtain ⟨j, t, rfl⟩ := Set.mem_iUnion.mp hs
    by_cases hj : j.val = 0
    · have hzero : j = 0 := Fin.ext hj
      subst j
      exact dgCoherentBarColumn_zero_degenerate_normalizedProjection R D F t
    · exact dgCoherentBarColumn_positive_degenerate_normalizedProjection R D F t j (by omega)

end SerrePositivity.InfinityCategories
