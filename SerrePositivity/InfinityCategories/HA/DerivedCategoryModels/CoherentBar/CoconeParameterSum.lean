module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterTerm
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.ParameterBoundarySum
/-!
概要：混合 HA 右辺のパラメーター側の和を、全標準面の高次 Hom の符号付き和へ同定する。
方針：全内部頂点の比較を有限和へ束ね、最後の切断補正を最終面へ移す。
規約：正次数の全余錐族を扱う。
使われ方：高次 Hom の微分が全標準面の境界に一致することの証明。
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

lemma dgCoherentBarCoconeFamily_parameter_sum {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) :
    HEq (∑ j : Fin (m + 1), _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
      (∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFaceColumn R D F hMC y c s a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_source R D F y c s)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_target R D F y c s)
    (fun j : Fin (m + 1) => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
    (fun j : Fin (m + 1) => (((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFaceColumn R D F hMC y c s j.castSucc -
        if j = Fin.last m then _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFaceColumn R D F hMC y c s
          (Fin.last (m + 1)) else 0))
    (fun j => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyFullTerm_parameter R D F hMC y c s j)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameter_boundary_sum] at h
  exact h

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
