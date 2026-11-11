module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyResidual
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftSourceSum
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComposite
/-!
概要：持ち上げ余錐について、全混合 HA 方程式から元の単体側の Leibniz 項を相殺する。
方針：最上成分を実 Hom へ輸送し、元の単体側の和の因数分解を適用する。
規約：パラメーター零次元も含め、元の theta の実微分を使う。
使われ方：高次 Hom の微分を、パラメーター側の有限和だけで表す。
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

lemma dgCoherentBarCoconeLiftSimplex_full_hom_heq {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).hom Finset.univ
      0 (Fin.last (n + m + 1)) (-((n + m : ℕ) : ℤ))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + m)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m)) (by simp; omega))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftColumn R D F c ⟨n, s⟩) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData
  have ht : HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftColumn R D F c ⟨n, s⟩)
      (T.hom Finset.univ 0 (Fin.last (n + m + 1)) (-(m : ℤ) - (n : ℤ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card (n + m)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min (n + m))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max (n + m)) (by simp; omega)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_source R D F c s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_target R D F c s) rfl _
  refine HEq.trans ?_ ht.symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.SimplexData.hom_heq_of_indices_degree T rfl rfl rfl (by omega)

lemma dgCoherentBarCoconeLiftHom_d_column_residual {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (s : I _⦋n⦌) :
    HEq (compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
      (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
      (z := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c)
      (differential R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)
      (show -(n : ℤ) + (-(m : ℤ) + 1) = -(m : ℤ) - (n : ℤ) + 1 by omega))
      (∑ j : Fin m, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).toSimplexData (j.natAdd n)) := by
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s
  have hx := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_source R D F c s
  have hz := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_target R D F c s
  have hk : -((n + m : ℕ) : ℤ) = -(m : ℤ) - (n : ℤ) := by omega
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D) hx hz hk _ _
    (dgCoherentBarCoconeLiftSimplex_full_hom_heq R D F c s)
  have hEq := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullSimplex_equation T
  rw [Fin.sum_univ_add] at hEq
  have hHA := hd.symm.trans (heq_of_eq hEq)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom_differential_columns R D F hMC c ⟨n, s⟩] at hHA
  have hCV := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_compose_degree_heq (R := R)
    (a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩) (b := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
    (c := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget R D F c)
    (p := -(n : ℤ) + 1) (q := -(m : ℤ))
    (k := -(m : ℤ) - (n : ℤ) + 1) (l := -((n + m : ℕ) : ℤ) + 1)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c)
    (differential R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩)) (by omega) (by omega)
  have hV := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq (R := R) (C := RightModule R D)
    rfl rfl (show -(m : ℤ) - (n : ℤ) + 1 = -((n + m : ℕ) : ℤ) + 1 by omega)
    (m : ℤ).negOnePow _ _ hCV
  have hSrc := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLift_source_sum R D F hMC c s
  have hV' := hV.trans hSrc.symm
  rw [← Int.negOnePow_neg (m : ℤ)] at hV'
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_add_cancel_heq hx.symm hz.symm
    (show -(m : ℤ) - (n : ℤ) + 1 = -((n + m : ℕ) : ℤ) + 1 by omega)
    _ _ _ _ hHA hV'

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
