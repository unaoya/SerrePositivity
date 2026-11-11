module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.AppendClosed
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomExchange
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NormalizedHomDegrees

/-!
概要：上界以下の単体に末尾付加し、それ以外では零とする全次数自然な作用素を作る。
方針：実正規化 graded 直和の Hom 同値で、閉じた次数 −1 の列を貼り合わせる。
規約：ここでは内部微分についての閉性だけを示す。
使われ方：有限 support に制限した bar 縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

lemma dgStrictAppendColumn_d {n : ℕ} (s : (nerve J) _⦋n⦌) (b : J)
    (hb : s.obj (Fin.last n) ≤ b) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) ⟨n, s⟩))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)))).d (-1) 0
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendColumn R D F s b hb) = 0 := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendColumn
  erw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictHom_postcompose_d R D,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendBlock_d R D F s b hb, map_zero]

lemma dgStrictNormalizedHomEquiv_apply (N : _root_.SerrePositivity.DifferentialGraded.RightModule R D) (q : ℤ)
    (z : (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))) N).X q)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex (nerve J)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) N q z s =
      (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)).f q z :=
  ConcreteCategory.congr_hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleCoproductHomDegreeIso_π R D
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) q s) z

def dgStrictAppendHomColumns (b : J) (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex (nerve J)) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) s))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)))).X (-1) :=
  by
    classical
    exact if hb : s.val.2.obj (Fin.last s.val.1) ≤ b then
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictAppendColumn R D F s.val.2 b hb else 0

def dgStrictAppendGradedHom (b : J) :
    (_root_.SerrePositivity.DifferentialGraded.moduleHom R D
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)))).X (-1) :=
  (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))) (-1)).symm
      (dgStrictAppendHomColumns R D F b)

lemma dgStrictAppendGradedHom_restrict (b : J)
    (s : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedIndex (nerve J)) :
    (eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedFamily R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)) s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))).f (-1)
      (dgStrictAppendGradedHom R D F b) = dgStrictAppendHomColumns R D F b s := by
  erw [← dgStrictNormalizedHomEquiv_apply R D F]
  exact congrFun ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedHomEquiv R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F)
    (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex R)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedGraded R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F))) (-1)).apply_symm_apply
        (dgStrictAppendHomColumns R D F b)) s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
