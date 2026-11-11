module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawVanishing
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_map_obj {a b n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) (i : Fin (a + b + 1 + 1)) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).obj i =
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)).obj i := by
  refine _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoin_cases (n := a) (m := b) (P := fun j =>
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).obj j =
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)).obj j) ?_ ?_ i
  · intro j
    have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) a => t.obj j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_map_left R D F hMC N f s α β)
    exact h
  · intro j
    have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) b => t.obj j)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_map_right R D F hMC N f s α β)
    exact h

lemma dgCoherentBarInverseRawData_map {a b n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β) := by
  classical
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSimplexData_ext
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_map_left R D F hMC N f s α β
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_map_right R D F hMC N f s α β
  · intro K L hK hL c d k hJ hc hd hk
    by_cases hi : Set.InjOn (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β)
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) : Set (Fin (a + b + 1 + 1)))
    · obtain ⟨hiK, hiL⟩ := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_injOn_subset_iff α β K L).mp hi
      exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_map_mixed_of_injOn R D F hMC N f s α β
        K L hK hL hiK hiL c d k hJ hc hd hk
    · rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_mixed_zero_of_not_injOn R D F hMC N f s α β
        K L hK hL hi c d k hJ hc hd hk,
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_not_inj _ _ _ _ _ _ _ _ _ _ hi
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card_ne_two_of_not_injOn α β K L hK hL hi)]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_zero_heq (A := R) (D := RightModule R D)
        (dgCoherentBarInverseRawData_map_obj R D F hMC N f s α β c)
        (dgCoherentBarInverseRawData_map_obj R D F hMC N f s α β d) rfl

lemma dgCoherentBarInverseSimplex_map {a b n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseSimplex R D F hMC N (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s) =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseSimplex R D F hMC N f s).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap α β) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact dgCoherentBarInverseRawData_map R D F hMC N f.val s α β

lemma dgCoherentBarInverseSimplex_left {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseSimplex R D F hMC N f s).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_left R D F hMC N f.val s

lemma dgCoherentBarInverseSimplex_right {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseSimplex R D F hMC N f s).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) N) m := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_right R D F hMC N f.val s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
