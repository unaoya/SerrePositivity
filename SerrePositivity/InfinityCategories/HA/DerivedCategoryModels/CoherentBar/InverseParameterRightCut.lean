module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeParameterRightCut
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseRawRightHom
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
/-!
概要：逆構成のパラメーターで切った HA 右因子を定値側の成分へ直し、最後の切断以外で消去する。
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

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseFullRight_parameter {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) N) (m + 1)).hom
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j) j.castSucc (Fin.last (m + 1))
        (2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j).card : ℤ)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_two j)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_min j) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_max j) rfl) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s)
  let L := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j
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
  have hPure := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_pure_right_hom_heq R D F hMC N f s L
    j.castSucc (Fin.last (m + 1)) (2 - (L.card : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_two j) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_min j)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_max j) rfl
  refine HEq.trans ?_ hPure
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T hSet.symm hj.symm hl.symm hd

lemma dgCoherentBarInverseFullRight_parameter_zero {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      (0 : _root_.SerrePositivity.DifferentialGraded.GradedHom R (N)
        (N)
        (2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail j).card : ℤ))) := by
  refine (dgCoherentBarInverseFullRight_parameter R D F hMC N f s j).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarConstant_hom_zero
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_card]
  have hne : j.val ≠ m := fun h => hj (Fin.ext h)
  have := j.isLt
  omega

lemma dgCoherentBarInverseFullRight_parameter_unit {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) ((Fin.last m).natAdd n))
      (_root_.SerrePositivity.DifferentialGraded.unitElement R (N)).val := by
  refine (dgCoherentBarInverseFullRight_parameter R D F hMC N f s (Fin.last m)).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarConstant_hom_unit
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarParameterTail_card]
  simp

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
