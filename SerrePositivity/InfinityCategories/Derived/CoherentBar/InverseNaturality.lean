module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawVanishing
/-!
概要：逆構成の実 HA 単体は、全ての面・退化による二変数の引き戻しに自然である。
方針：純粋な面と混合成分を比較し、非単射分岐では退化消滅を使う。
規約：全単調写像を扱い、部分集合上の単射性だけで場合分けする。
使われ方：逆余錐族の単体的な組み立て。
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

lemma dgCoherentBarInverseRawData_map_obj {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) (i : Fin (a + b + 1 + 1)) :
    (dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).obj i =
    ((dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β)).obj i := by
  refine dgCoherentBarJoin_cases (n := a) (m := b) (P := fun j =>
    (dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).obj j =
    ((dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β)).obj j) ?_ ?_ i
  · intro j
    have h := congrArg (fun t : SimplexData R (RightModule R D) a => t.obj j)
      (dgCoherentBarInverseRawData_map_left R D F hMC N f s α β)
    exact h
  · intro j
    have h := congrArg (fun t : SimplexData R (RightModule R D) b => t.obj j)
      (dgCoherentBarInverseRawData_map_right R D F hMC N f s α β)
    exact h

lemma dgCoherentBarInverseRawData_map {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s) =
    (dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β) := by
  classical
  apply dgCoherentBarJoinSimplexData_ext
  · exact dgCoherentBarInverseRawData_map_left R D F hMC N f s α β
  · exact dgCoherentBarInverseRawData_map_right R D F hMC N f s α β
  · intro K L hK hL c d k hJ hc hd hk
    by_cases hi : Set.InjOn (dgCoherentBarJoinOrderMap α β)
        ((dgCoherentBarJoinSubset K L) : Set (Fin (a + b + 1 + 1)))
    · obtain ⟨hiK, hiL⟩ := (dgCoherentBarJoinOrderMap_injOn_subset_iff α β K L).mp hi
      exact dgCoherentBarInverseRawData_map_mixed_of_injOn R D F hMC N f s α β
        K L hK hL hiK hiL c d k hJ hc hd hk
    · rw [dgCoherentBarInverseRawData_mixed_zero_of_not_injOn R D F hMC N f s α β
        K L hK hL hi c d k hJ hc hd hk,
        SimplexData.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi
          (dgCoherentBarJoinSubset_card_ne_two_of_not_injOn α β K L hK hL hi)]
      exact gradedHom_zero_heq (A := R) (D := RightModule R D)
        (dgCoherentBarInverseRawData_map_obj R D F hMC N f s α β c)
        (dgCoherentBarInverseRawData_map_obj R D F hMC N f s α β d) rfl

lemma dgCoherentBarInverseSimplex_map {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    dgCoherentBarInverseSimplex R D F hMC N (DGNerve.PinchedHom.LinearSimplex.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s) =
    (dgCoherentBarInverseSimplex R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β) := by
  apply DGNerve.Simplex.ext
  exact dgCoherentBarInverseRawData_map R D F hMC N f.val s α β

lemma dgCoherentBarInverseSimplex_left {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseSimplex R D F hMC N f s).pullback (dgCoherentBarJoinLeft n m) =
      coherentDiagramSimplex F s := by
  apply DGNerve.Simplex.ext
  exact dgCoherentBarInverseRawData_left R D F hMC N f.val s

lemma dgCoherentBarInverseSimplex_right {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (dgCoherentBarInverseSimplex R D F hMC N f s).pullback (dgCoherentBarJoinRight n m) =
      InfinityCategories.PinchedHom.constant (X := dgNerve R (RightModule R D))
        (Simplex.vertex (A := R) N) m := by
  apply DGNerve.Simplex.ext
  exact dgCoherentBarInverseRawData_right R D F hMC N f.val s

end SerrePositivity.InfinityCategories
