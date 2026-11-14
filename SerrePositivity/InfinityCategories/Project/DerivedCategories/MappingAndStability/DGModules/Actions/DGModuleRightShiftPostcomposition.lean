module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleShiftUnitNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRepresentableDerivedPrimitives

/-! # 右シフト閉射と後合成の全次数の比較

概要：右シフト閉射の後合成を、元の全次数 Hom の後合成へ戻す。
方針：包含の自然性・結合則と Hom whiskering の斉次公式を使う。
規約：主導来零性は具体的な原始元から導く。使われ方：商の斉次境界性の比較写像への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 閉加群射による Hom whiskering の斉次成分は通常順の後合成。 -/
lemma dgModulePostcompose_graded {L M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (g : M ⟶ N) (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) L)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) n) :
    (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) L g).f n f =
      _root_.SerrePositivity.DifferentialGraded.compose A (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) M N g).val f (add_zero n) := by
  have h := congrArg (fun l => l f) (Cochain.congr_v
    (_root_.SerrePositivity.DifferentialGraded.modulePostcompositionMap_closed A D L g) n n (add_zero n))
  rw [_root_.SerrePositivity.DifferentialGraded.modulePostcompositionMap_apply, Cochain.ofHom_v] at h
  exact h.symm

/-- shift 閉射を shift した閉射で後合成した cycle は、元の斉次後合成の右 shift。 -/
lemma dgModuleClosedRightShift_postcompose_cycle {L M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D} (n : ℤ)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) L)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) n) (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) (g : M ⟶ N) :
    (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) L (N⟦n⟧)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift A D n f hf ≫ g⟦n⟧')).val =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift A D n ((eHomWhiskerLeft (Complex A) L g).f n f) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.closedHom_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift_cycle, dgModulePostcompose_graded]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_neg_cancel n) (add_zero (-n)) (zero_add 0),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleShiftIn_naturality,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero n) (zero_add (-n)) (add_neg_cancel n)]
  rfl

/-- 元の後合成の原始元から、shift 閉射の後合成の主導来零性を得る。 -/
lemma dgModuleClosedRightShift_postcompose_zero_of_primitive {L M N : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D}
    (hL : _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective A D L) (n k : ℤ) (hkn : k + 1 = n)
    (f : _root_.SerrePositivity.DifferentialGraded.GradedHom A (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) L)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) M) n) (hf : _root_.SerrePositivity.DifferentialGraded.differential A f = 0) (g : M ⟶ N)
    (ha : ∃ a : (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) L)
      (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).X k,
      (_root_.SerrePositivity.DifferentialGraded.moduleHom A D (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) L)
        (ForgetEnrichment.to (_root_.SerrePositivity.DifferentialGraded.Complex A) N)).d k n a =
          (eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) L g).f n f) :
    (moduleToDerived A D).map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift A D n f hf ≫ g⟦n⟧') = 0 := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleProjectiveDerived_zero_iff_primitive A D hL _).mpr
  obtain ⟨a, ha⟩ := ha
  obtain ⟨h, hh⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHomRightShift_exists_primitive_iff A D n k hkn
    ((eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) L g).f n f)).mpr ⟨a, ha⟩
  exact ⟨h, hh.trans (dgModuleClosedRightShift_postcompose_cycle A D n f hf g).symm⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
