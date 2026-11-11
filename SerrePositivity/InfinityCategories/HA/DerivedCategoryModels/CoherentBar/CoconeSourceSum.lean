module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeSourceTerm
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeFullCoefficient
/-!
概要：混合 HA 右辺の元の単体側の和を、高次 Hom と native 列の微分の合成へ同定する。
方針：全項の因数分解を有限和へ束ね、native 単体の実 HA 方程式を適用する。
規約：内部頂点のない元の単体も含む。
使われ方：Hom の Leibniz 項と HA 右辺の元の単体側を相殺する。
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

lemma dgCoherentBarCoconeFamily_source_sum {m n : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F y) _⦋m⦌) (s : I _⦋n⦌) :
    HEq (∑ i : Fin n, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData (i.castAdd m))
      ((m : ℤ).negOnePow •
        compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩)
          (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
          (z := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y)
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y c)
          (differential R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩))
          (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega)) := by
  let T := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex R D F y c s).toSimplexData
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
  let ρ := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt R D F hMC y c s
  have hFront := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_left R D F y c s).trans
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_front R D F hMC s).symm
  have hx : T.obj 0 = S.obj 0 :=
    congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R (RightModule R D) n => a.obj 0) hFront
  have hz : T.obj (Fin.last (n + m + 1)) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R (RightModule R D) y :=
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilySimplex_target R D F y c s
  have hSum := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.sum_heq_of_obj_eq hx hz
    (fun i : Fin n => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm T (i.castAdd m))
    (fun i : Fin n => (m : ℤ).negOnePow •
      compose R ρ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm S i)
        (show (-(n : ℤ) + 1) + -(m : ℤ) = -((n + m : ℕ) : ℤ) + 1 by omega))
    (fun i => _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyFullTerm_source R D F hMC y c s i)
  rw [← Finset.smul_sum, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_right,
    ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullSimplex_equation (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s)] at hSum
  have hxs := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_source R D F hMC s
  have hys := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last R D F hMC s
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_differential_heq (A := R) (D := RightModule R D) hxs hys rfl _ _
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_full_hom_heq R D F hMC s)
  have hComp := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    hxs hys rfl rfl rfl rfl
    (p := -(n : ℤ) + 1) (q := -(m : ℤ)) (k := -((n + m : ℕ) : ℤ) + 1)
    (p' := -(n : ℤ) + 1) (q' := -(m : ℤ)) (k' := -((n + m : ℕ) : ℤ) + 1)
    ρ
    (differential R ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).hom Finset.univ
      0 (Fin.last (n + 1)) (-(n : ℤ)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n) (by simp; omega)))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHom R D F hMC y c)
    (differential R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC ⟨n, s⟩))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeFamilyHomAt_heq R D F hMC y c s) hd (by omega) (by omega)
  refine hSum.trans ?_
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarHom_units_smul_heq hxs rfl rfl (m : ℤ).negOnePow _ _ hComp

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
