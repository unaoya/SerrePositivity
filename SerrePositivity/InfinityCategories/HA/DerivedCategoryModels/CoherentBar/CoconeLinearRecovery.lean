module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomSpaceComparison
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyFactorization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinSimplexDataExt
/-!
概要：比較射の線形成分から全パラメーター部分単体の Hom と混合 HA 単体を一意に回収する。
方針：次数符号を二回作用させて消し、純粋な面と混合因数分解の一意性を使う。
規約：写像空間の全次数を扱い、零次の一意性で代用しない。
使われ方：全余錐空間の比較射の単射性。
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
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeLinearData_subset_recovery {n : ℕ}
    (c d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋n⦌)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y d)
    (J : Finset (Fin (n + 1))) (r : ℕ) (hc : J.card = r + 1) (hJ : J.Nonempty) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y c J r hc =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom R D F hMC y d J r hc := by
  have hk : -(r : ℤ) = 1 - (J.card : ℤ) := by rw [hc]; push_cast; omega
  have hRaw := congrArg (fun f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y) n =>
      f.component J (-(r : ℤ)) hJ hk) h
  have hScalar := eq_of_heq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y c
    J (-(r : ℤ)) hJ hk r hc).symm.trans ((heq_of_eq hRaw).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetHom_heq R D F hMC y d J (-(r : ℤ)) hJ hk r hc)))
  have hTwice := congrArg (fun z => (r : ℤ).negOnePow • z) hScalar
  simpa only [smul_smul, Int.units_mul_self, one_smul] using hTwice

lemma dgCoherentBarCoconeFamilySimplex_eq_of_linearData {m n : ℕ}
    (c d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m⦌)
    (h : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y c =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLinearData R D F hMC y d) (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y d s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSimplexData_ext
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_left R D F y c s).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_left R D F y d s).symm)
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_right R D F y c s).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_right R D F y d s).symm)
  · intro K L hK hL a b k hJ ha hb hk
    let r := K.card - 1
    let l := L.card - 1
    have hcK : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
    have hcL : L.card = l + 1 := by have := Finset.card_pos.mpr hL; dsimp [l]; omega
    have hPhi := dgCoherentBarCoconeLinearData_subset_recovery R D F hMC y c d h L l hcL hL
    dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSubsetParameterHom] at hPhi
    have hRho : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map
          (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op c) s =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y).map
            (SimplexCategory.mkHom (L.orderEmbOfFin hcL).toOrderHom).op d) s := by
      unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt
      rw [hPhi]
    have hC := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_mixed_factorization R D F hMC y
      (r := r) (l := l) c s K L hcK hcL hK a b k hJ ha hb hk
    have hD := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_mixed_factorization R D F hMC y
      (r := r) (l := l) d s K L hcK hcL hK a b k hJ ha hb hk
    rw [hRho] at hC
    exact hC.trans hD.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
