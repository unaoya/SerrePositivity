module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.AppendHom

/-!
概要：上界付き末尾付加作用素は graded bar の内部微分について閉じている。
方針：各非退化列で判定し、閉零包含による Hom 制限の微分可換式を使う。
規約：MC 微分による縮約式は別に証明する。
使われ方：局所 bar 縮約の内部微分項の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

lemma dgStrictAppendHomColumns_d (b : J)
    (s : dgCoherentBarNormalizedIndex (nerve J)) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F) s))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).d (-1) 0
      (dgStrictAppendHomColumns R D F b s) = 0 := by
  classical
  unfold dgStrictAppendHomColumns
  split_ifs with hb
  · exact dgStrictAppendColumn_d R D F s.val.2 b hb
  · exact map_zero _

lemma dgStrictAppendGradedHom_d (b : J) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).d (-1) 0
      (dgStrictAppendGradedHom R D F b) = 0 := by
  apply (dgCoherentBarNormalizedHomEquiv R D (dgCoherentBarStrictDiagram R D F)
    (ForgetEnrichment.to (Complex R)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))) 0).injective
  rw [map_zero]
  funext s
  erw [dgStrictNormalizedHomEquiv_apply R D F]
  have h := ConcreteCategory.congr_hom
    ((eHomWhiskerRight (Complex R)
      (Sigma.ι (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F)) s)
      (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))).comm (-1) 0)
    (dgStrictAppendGradedHom R D F b)
  change (moduleHom R D
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F) s))
      (ForgetEnrichment.to (Complex R)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F)))).d (-1) 0
      ((eHomWhiskerRight (Complex R)
        (Sigma.ι (dgCoherentBarNormalizedFamily R D (dgCoherentBarStrictDiagram R D F)) s)
        (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))).f (-1)
          (dgStrictAppendGradedHom R D F b)) = _ at h
  erw [← h, dgStrictAppendGradedHom_restrict R D F b s,
    dgStrictAppendHomColumns_d R D F b s]
  rfl

end SerrePositivity.InfinityCategories
