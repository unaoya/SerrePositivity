module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FiniteBounds

/-!
概要：coherent G の正規化 bar の全要素に有限単体 support と次元上限を与える。
方針：実 graded 余積の次数ごとの普遍性を使い、有限集合の最大次元を取る。
規約：G は元の HA 成分を全て持ち、strict 性を仮定しない。
使われ方：非有界複体で最大単体次元を下げる帰納法。
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

lemma dgCoherentBarNormalizedDegree_finiteSupport (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G)) :
    ∃ (t : Finset (dgCoherentBarNormalizedIndex I))
      (a : ∀ s, (moduleDegreeEvaluation R D x q).obj
        (dgCoherentBarNormalizedFamily R D G s)),
      ∑ s ∈ t, ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s)) (a s) = z :=
  moduleCofan_element_rep R
    (fun s => (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedFamily R D G s)) _
    (moduleCoproductDegreeIsColimit R D (dgCoherentBarNormalizedFamily R D G) x q) z

lemma dgCoherentBarNormalizedDegree_boundedSupport (x : D) (q : ℤ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarNormalizedGraded R D G)) :
    ∃ (n : ℕ) (t : Finset (dgCoherentBarNormalizedIndex I))
      (a : ∀ s, (moduleDegreeEvaluation R D x q).obj
        (dgCoherentBarNormalizedFamily R D G s)),
      (∀ s ∈ t, s.val.1 ≤ n) ∧
      ∑ s ∈ t, ((moduleDegreeEvaluation R D x q).map
        (Sigma.ι (dgCoherentBarNormalizedFamily R D G) s)) (a s) = z := by
  classical
  obtain ⟨t, a, ha⟩ := dgCoherentBarNormalizedDegree_finiteSupport R D G x q z
  refine ⟨t.sup (fun s => s.val.1), t, a, ?_, ha⟩
  exact fun s hs => Finset.le_sup (f := fun s => s.val.1) hs

end SerrePositivity.InfinityCategories
