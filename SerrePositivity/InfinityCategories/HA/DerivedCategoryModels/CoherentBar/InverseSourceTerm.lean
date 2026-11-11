module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceLeftCut
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseSourceRightCut
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.PostcompositionAlgebra
/-!
概要：逆構成の混合 HA の元の内部頂点の一項を、高次 Hom による native HA 項の後合成へ直す。
方針：削除・左右切断の三つの比較と、全次数合成の結合則と符号を合わせる。
規約：元の theta の微分を変えず、実加群の全 HA 成分を使う。
使われ方：元の単体側の和と高次 Hom の Leibniz 項の相殺。
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
  (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D)

lemma dgCoherentBarInverseFullTerm_source {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (i : Fin n) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s) (i.castAdd m))
      ((m : ℤ).negOnePow •
        compose R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHomAt R D F hMC N f s)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData i)
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s)
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let ρ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullHomAt R D F hMC N f s
  let p : ℤ := 2 - (((Finset.univ : Finset (Fin (n + 2))).filter
    (· ≤ i.succ.castSucc)).card : ℤ)
  let q : ℤ := 2 - (((Finset.univ : Finset (Fin (n + 2))).filter
    (i.succ.castSucc ≤ ·)).card : ℤ)
  let pT : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    (· ≤ (i.castAdd m).succ.castSucc)).card : ℤ)
  let qT : ℤ := 2 - (((Finset.univ : Finset (Fin (n + m + 2))).filter
    ((i.castAdd m).succ.castSucc ≤ ·)).card : ℤ)
  have hp : pT = p := by
    dsimp only [pT, p]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft_card, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft_card]
    rfl
  have hq : qT = q + -(m : ℤ) := by
    dsimp only [qT, q]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight_card, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight_card]
    have := i.isLt
    simp only [Fin.val_castAdd]
    omega
  have hkS : p + q = -(n : ℤ) + 1 := by
    dsimp only [p, q]
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft_card, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight_card]
    have := i.isLt
    omega
  have hkT : pT + qT = -((n + m : ℕ) : ℤ) + 1 := by rw [hp, hq]; omega
  have hFront := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_left R D F hMC N f s).trans
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_front R D F hMC s)).symm
  have hx0 := congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) n => a.obj 0) hFront
  have hx : T.obj 0 = S.obj 0 := hx0
  have hy0 := congrArg
    (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) n => a.obj i.succ) hFront
  have hy : T.obj (i.castAdd m).succ.castSucc = S.obj i.succ.castSucc := hy0
  have hz : T.obj (Fin.last (n + m + 1)) = N :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData_target R D F hMC N f s
  have hCut := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hx hy hz hp hq rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight T (i.castAdd m)) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft T (i.castAdd m))
    (compose R ρ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight S i) rfl) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft S i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullRight_source R D F hMC N f s i)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullLeft_source R D F hMC N f s i)
    hkT (show p + (q + -(m : ℤ)) = -((n + m : ℕ) : ℤ) + 1 by omega)
  have hAssoc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullLeft S i) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullRight S i) ρ hkS rfl
    (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)
  change HEq (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm T (i.castAdd m))
    ((m : ℤ).negOnePow • compose R ρ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm S i) _)
  rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_eq, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_eq,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_right, smul_smul,
    ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm_sign_left n m i, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sub_right]
  apply _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq hx hz rfl
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_sub_heq hx hz rfl
  · exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseFullErase_source R D F hMC N f s i
  · exact hCut.trans (heq_of_eq hAssoc.symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
