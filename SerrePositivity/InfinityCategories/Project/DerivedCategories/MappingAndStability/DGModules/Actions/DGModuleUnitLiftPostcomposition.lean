module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGClosedPostcompositionChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleUnitPostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.DGComposition.DGClosedHomWhiskerNaturality
/-!
概要：R の代表加群からの全 Hom 後合成を、対象宇宙の持ち上げの前後で厳密に照合する。
方針：同じ実 dg 関手の Hom 自然性と、その恒等 Hom 写像を使う。
規約：準同型は全次数で保つ。使われ方：基礎空間関手による実準同型の反転。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v)
/-- 同じ対象宇宙の持ち上げは、R からの全 Hom 後合成そのものを変えない。 -/
lemma dgHomModuleUnitPostcomp_lift {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})).onClosed.map f) =
      eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex R)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)) f := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1}))
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (_root_.SerrePositivity.DifferentialGraded.representable R PUnit.unit)) f
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp, Category.comp_id, Category.id_comp] at h
  exact h.symm
/-- 元の加群の準同型は、持ち上げた同じ R からの全 Hom 後合成でも準同型。 -/
lemma dgHomModuleUnitPostcomp_lift_quasiIso {M N : _root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1}}
    (f : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) M ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) N)
    (hf : _root_.SerrePositivity.DifferentialGraded.moduleQuasiIso R PUnit.{1} f) :
    QuasiIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPostcomposition R
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
      (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomModuleUnit R D)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R
        (_root_.SerrePositivity.DifferentialGraded.RightModule R PUnit.{1})).onClosed.map f)) := by
  rw [dgHomModuleUnitPostcomp_lift]
  exact _root_.SerrePositivity.DifferentialGraded.moduleHomotopicallyProjective_postcompose_quasiIso R PUnit.{1}
    (_root_.SerrePositivity.DifferentialGraded.representable_homotopicallyProjective R PUnit.{1} PUnit.unit) f hf
end SerrePositivity.InfinityCategories.Project.DerivedCategories
