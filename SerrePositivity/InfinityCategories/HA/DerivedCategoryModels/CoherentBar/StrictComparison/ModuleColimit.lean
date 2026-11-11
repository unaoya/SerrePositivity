module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexColimit
public import SerrePositivity.DifferentialGraded.Module.ActionLimits
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-!
概要：strict filtered 余極限は、対象ごとの dg 加群擬同型を保存する。
方針：評価と余極限の標準同型を介し、非有界加群複体の完全 filtered colim へ戻す。
規約：元の全 dg 加群作用を持つ strict 余極限を使う。
使われ方：局所 bar 縮約の擬同型を大域へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [SmallCategory J]

lemma dgStrictModuleColimitIso_naturality
    {F G : J ⥤ ModuleCategory R D} (τ : F ⟶ G) (x : D) :
    (moduleEvaluation R D x).map (colim.map τ) ≫
        (moduleEvaluationColimitIso R D G x).hom =
      (moduleEvaluationColimitIso R D F x).hom ≫
        colim.map (Functor.whiskerRight τ (moduleEvaluation R D x)) := by
  exact (preservesColimitNatIso (moduleEvaluation R D x)).hom.naturality τ

lemma dgStrictFilteredModuleColimit_quasiIso [IsFiltered J]
    {F G : J ⥤ ModuleCategory R D} (τ : F ⟶ G)
    (hτ : ∀ j, moduleQuasiIso R D (τ.app j)) : moduleQuasiIso R D (colim.map τ) := by
  intro x
  have hx : ∀ j, QuasiIso ((Functor.whiskerRight τ (moduleEvaluation R D x)).app j) :=
    fun j => hτ j x
  have h := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictFilteredColimit_quasiIso R
    (Functor.whiskerRight τ (moduleEvaluation R D x)) hx
  letI := h
  apply (quasiIso_iff_comp_right _ (moduleEvaluationColimitIso R D G x).hom).mp
  rw [dgStrictModuleColimitIso_naturality R D τ x]
  infer_instance

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
