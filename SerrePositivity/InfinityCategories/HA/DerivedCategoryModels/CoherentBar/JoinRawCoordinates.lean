module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawGluing
/-!
概要：貼り合わせた join 単体データの全混合成分を計算する。
方針：左右への分割が元の矩形を回収することから、混合分岐の実輸送を消す。
規約：端点と次数を異種等号で保持する。
使われ方：逆比較の HA 方程式と成分復元。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

lemma dgCoherentBarJoinMixedData_component_heq {n m : ℕ}
    {s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n} {t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C m} (f : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DGCoherentBarJoinMixedData s t)
    {K K' : Finset (Fin (n + 1))} {L L' : Finset (Fin (m + 1))}
    (hKK' : K = K') (hLL' : L = L')
    (hK : K.Nonempty) (hK' : K'.Nonempty) (hL : L.Nonempty) (hL' : L'.Nonempty)
    (k : ℤ) (hk : k = 2 - (K.card : ℤ) - (L.card : ℤ))
    (hk' : k = 2 - (K'.card : ℤ) - (L'.card : ℤ)) :
    HEq (f K L hK hL k hk) (f K' L' hK' hL' k hk') := by
  cases hKK'
  cases hLL'
  rfl

lemma dgCoherentBarJoinRawData_mixed_hom_heq {n m : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C m) (f : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DGCoherentBarJoinMixedData s t)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData s t f).hom (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L)
      a b k hJ ha hb hk)
      (f K L hK hL k (by rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_card] at hk; push_cast at hk; omega)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart_subset, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart_subset,
    dite_eq_left hK, dite_eq_left hL]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (A := R) (D := C) _ _ _ _).trans
    (dgCoherentBarJoinMixedData_component_heq f
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart_subset K L) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart_subset K L)
      _ hK _ hL k _ _)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
