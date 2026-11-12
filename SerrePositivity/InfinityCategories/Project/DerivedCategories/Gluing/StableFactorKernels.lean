module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableObjects
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorZeroTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorSubcategories
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ContractingElementCriterion
/-!
概要：既存の二つの実 dg 因子は、安定 gluing の元射影の零対象核である。
方針：H⁰ の零性を同じ恒等射の収縮元へ移し、実 nerve の零性と宇宙輸送を使う。
規約：因子の対象条件と射影を変更しない。
使われ方：順序 ⟨D,C⟩ の半直交分解と K-8b の射影核の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
lemma dgGluingFactorIsZero_iff_isZeroVertex (x : C) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C x ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero_iff_boundary, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_iff_contractingElement]
  change Nonempty (_root_.Homotopy (eId (_root_.SerrePositivity.DifferentialGraded.Complex R) x) 0) ↔ _
  simpa [_root_.SerrePositivity.DifferentialGraded.unitElement, _root_.SerrePositivity.DifferentialGraded.cycleFromUnit] using
    (_root_.SerrePositivity.DifferentialGraded.unit_homotopy_boundary (_root_.SerrePositivity.DifferentialGraded.homObject R C x x) (eId (_root_.SerrePositivity.DifferentialGraded.Complex R) x) 0)
variable [Small.{u} C] (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]
  (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
lemma dgGluingCFactor_iff_stableRightKernel (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R D X.right ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) := by
  rw [dgGluingFactorIsZero_iff_isZeroVertex]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseRightNerve]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex]
  change _ ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := (SSet.uliftFunctor.{max (u + 1) v w,max u w}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.right))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _
lemma dgGluingDFactor_iff_stableLeftKernel (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorIsZero R C X.left ↔
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌)
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) := by
  rw [dgGluingFactorIsZero_iff_isZeroVertex]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseLeftNerve]
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_vertex]
  change _ ↔ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := (SSet.uliftFunctor.{max (u + 1) v w,max u v}).obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X.left))
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.isZeroVertex_iff_ulift _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
