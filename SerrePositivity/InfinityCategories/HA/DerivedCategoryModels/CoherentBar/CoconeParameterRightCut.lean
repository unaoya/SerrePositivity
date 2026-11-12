module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterFaces
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
/-!
概要：パラメーターで切った HA 右因子を定値側の成分へ直し、最後の切断以外で消去する。
方針：右区間の尾部集合の像と、定値単体の単位・零の成分公式を使う。
規約：末尾の切断では実 dg 単位を保持する。
使われ方：パラメーター側の切断合成を最後の標準面へまとめる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial

def dgCoherentBarParameterTail {m : ℕ} (j : Fin (m + 1)) : Finset (Fin (m + 2)) :=
  Finset.univ.filter (j.castSucc ≤ ·)

lemma dgCoherentBarParameterTail_card {m : ℕ} (j : Fin (m + 1)) :
    (dgCoherentBarParameterTail j).card = (m + 1) - j.val + 1 :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTail_card (m + 1) j.castSucc

lemma dgCoherentBarParameterTail_two {m : ℕ} (j : Fin (m + 1)) :
    2 ≤ (dgCoherentBarParameterTail j).card := by
  rw [dgCoherentBarParameterTail_card]
  have := j.isLt
  omega

lemma dgCoherentBarParameterTail_min {m : ℕ} (j : Fin (m + 1)) :
    j.castSucc = (dgCoherentBarParameterTail j).min'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (dgCoherentBarParameterTail_two j)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.right_min (Finset.mem_univ _) _

lemma dgCoherentBarParameterTail_max {m : ℕ} (j : Fin (m + 1)) :
    Fin.last (m + 1) = (dgCoherentBarParameterTail j).max'
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (dgCoherentBarParameterTail_two j)) := by
  apply le_antisymm
  · exact Finset.le_max' _ _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.le_last _⟩)
  · exact Fin.le_last _

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeFamilyFullRight_parameter {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y (m + 1)).hom
        (dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((dgCoherentBarParameterTail j).card : ℤ)) (dgCoherentBarParameterTail_two j)
        (dgCoherentBarParameterTail_min j) (dgCoherentBarParameterTail_max j) rfl) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  let L := dgCoherentBarParameterTail j
  have hj : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n (m + 1) j.castSucc =
      (j.natAdd n).succ.castSucc := Fin.ext (by
    change n + 1 + j.val = n + j.val + 1
    omega)
  have hl : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n (m + 1) (Fin.last (m + 1)) =
      Fin.last (n + (m + 1) + 1) := Fin.ext (by
    change n + 1 + (m + 1) = n + (m + 1) + 1
    omega)
  have hSet : L.image (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n (m + 1)) =
      (Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
        ((j.natAdd n).succ.castSucc ≤ ·) := by
    have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_filter_right_le
      (Finset.univ : Finset (Fin (n + 1)))
      (Finset.univ : Finset (Fin (m + 2))) j.castSucc
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset_univ, hj] at h
    exact h.symm
  have hd : (2 - (((Finset.univ : Finset (Fin (n + (m + 1) + 2))).filter
      ((j.natAdd n).succ.castSucc ≤ ·)).card : ℤ)) = 2 - (L.card : ℤ) := by
    rw [← hSet, Finset.card_image_of_injective _
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight_injective n (m + 1))]
  have hPure := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_pure_right_hom_heq R D F y c s L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (dgCoherentBarParameterTail_two j) (dgCoherentBarParameterTail_min j)
    (dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarCoconeFamilyFullRight_parameter_zero {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (j.natAdd n))
      (0 : GradedHom R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y)
        (2 - ((dgCoherentBarParameterTail j).card : ℤ))) := by
  refine (dgCoherentBarCoconeFamilyFullRight_parameter R D F y c s j).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarConstant_hom_zero
  rw [dgCoherentBarParameterTail_card]
  have hne : j.val ≠ m := fun h => hj (Fin.ext h)
  have := j.isLt
  omega

lemma dgCoherentBarCoconeFamilyFullRight_parameter_unit {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m + 1⦌) (s : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData ((Fin.last m).natAdd n))
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y)).val := by
  refine (dgCoherentBarCoconeFamilyFullRight_parameter R D F y c s (Fin.last m)).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarConstant_hom_unit
  rw [dgCoherentBarParameterTail_card]
  simp

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
