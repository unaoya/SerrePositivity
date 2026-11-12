module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredFullEquation
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseEquationTransfer
/-!
概要：余錐族から、全部分集合の方程式を満たす一点下の実 HA 単体を回収する。
方針：混合集合では昇順部分単体の全頂点方程式を移し、純粋面では既存の HA 単体を使う。
規約：元の theta と正規化加群の公開型を保持する。
使われ方：標準 Hom の族と左右 Hom 比較の実単体による照合。
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
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeRecoveredRawData_equation_univ {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).Equation Finset.univ := by
  intro a b k hJ ha hb hk
  have ha0 : a = 0 := ha.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (0 + n)).symm
  have hbl : b = Fin.last (0 + n + 1) := hb.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (0 + n)).symm
  have hk0 : k = -((0 + n : ℕ) : ℤ) := by
    simp only [Finset.card_univ, Fintype.card_fin] at hk
    omega
  cases ha0
  cases hbl
  cases hk0
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_full_equation R D F hMC c

lemma dgCoherentBarCoconeRecoveredRawData_equation_mixed {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (K : Finset (Fin 1)) (L : Finset (Fin (n + 1)))
    (hK : K.Nonempty) (hL : L.Nonempty) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).Equation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) := by
  have hK0 := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFinOneSubset_eq_univ K hK
  subst K
  let l := L.card - 1
  have hcL : L.card = l + 1 := by have := Finset.card_pos.mpr hL; dsimp [l]; omega
  let β := (L.orderEmbOfFin hcL).toOrderHom
  let γ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) β
  have hiγ : Function.Injective γ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap_injective
    (OrderHom.id : Fin 1 →o Fin 1) β Function.injective_id (L.orderEmbOfFin hcL).injective
  have hMap := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map R D F hMC c β
  have hEq := dgCoherentBarCoconeRecoveredRawData_equation_univ R D F hMC
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom β).op c)
  have hImage := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarEquation_image_of_pullback
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c) γ _ hMap.symm Finset.univ hEq hiγ.injOn
  have hImg : (Finset.univ : Finset (Fin (0 + l + 1 + 1))).image γ =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)) L := by
    rw [← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ 0 l, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_map]
    have hid : (Finset.univ : Finset (Fin 1)).image (OrderHom.id : Fin 1 →o Fin 1) =
        Finset.univ := by
      change (Finset.univ : Finset (Fin 1)).image id = Finset.univ
      exact Finset.image_id
    rw [hid]
    exact congrArg (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset (Finset.univ : Finset (Fin 1)))
      (L.image_orderEmbOfFin_univ hcL)
  simpa only [hImg] using hImage

lemma dgCoherentBarCoconeRecoveredRawData_equation {n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (J : Finset (Fin (0 + n + 1 + 1))) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c).Equation J := by
  classical
  let K := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeftPart 0 n J
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRightPart 0 n J
  have hSet : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L = J := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_parts 0 n J
  by_cases hK : K.Nonempty
  · by_cases hL : L.Nonempty
    · simpa only [hSet] using
        dgCoherentBarCoconeRecoveredRawData_equation_mixed R D F hMC c K L hK hL
    · have hLE : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
      have hImg : K.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft 0 n) = J := by
        simpa only [hLE, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.union_empty] using hSet
      have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.equation_image_of_pullback
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft 0 n)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_left R D F hMC c) K
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft_injective 0 n).injOn
      simpa only [hImg] using he
  · have hKE : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    have hImg : L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n) = J := by
      simpa only [hKE, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset, Finset.image_empty, Finset.empty_union] using hSet
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.equation_image_of_pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋n⦌) c)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_right R D F hMC c) L
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective 0 n).injOn
    simpa only [hImg] using he

def dgCoherentBarCoconeRecoveredSimplex {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) (0 + n + 1) where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData R D F hMC c
  equation J a b k hJ ha hb hk :=
    dgCoherentBarCoconeRecoveredRawData_equation R D F hMC c J a b k hJ ha hb hk

lemma dgCoherentBarCoconeRecoveredSimplex_left {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredSimplex R D F hMC c).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft 0 n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_left R D F hMC c

lemma dgCoherentBarCoconeRecoveredSimplex_right {n : ℕ} (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) :
    (dgCoherentBarCoconeRecoveredSimplex R D F hMC c).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight 0 n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋n⦌) c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_right R D F hMC c

lemma dgCoherentBarCoconeRecoveredSimplex_map {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconeRecoveredSimplex R D F hMC
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom α).op c) =
    (dgCoherentBarCoconeRecoveredSimplex R D F hMC c).pullback
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinOrderMap (OrderHom.id : Fin 1 →o Fin 1) α) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeRecoveredRawData_map R D F hMC c α

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
