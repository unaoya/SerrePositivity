module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialUniqueness

/-!
概要：元の全反対要素圏上の実 cone を、点とその nerve の join からの大域射として構成する。
方針：同じ coslice 写像を uncurry し、先端・通常図式・全単体への制限を厳密に回収する。
規約：同じ元の先端の元の probe と全通常 frame 図式を保つ。使われ方：元の屋根との大域比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

def strictRawModuleTensorConeJoin :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (strictRawModuleTensorConeUnderMap A X P Q)

lemma strictRawModuleTensorConeJoin_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorConePoint A X P :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed (strictRawModuleTensorConeUnderMap A X P Q)

lemma strictRawModuleTensorConeJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorConeJoin A X P Q = strictRawModuleTensorElementNerveDiagram A X P Q := by
  rw [strictRawModuleTensorConeJoin, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection,
    strictRawModuleTensorConeUnderMap_projection]

lemma strictRawModuleTensorConeJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (SSet.yonedaEquiv.symm c) ≫
      strictRawModuleTensorConeJoin A X P Q =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.pointJoinStdSimplexIso n).hom ≫
        (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))))).symm
          (strictRawModuleTensorConeSimplex A X P Q c) := by
  rw [strictRawModuleTensorConeJoin, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    SSet.yonedaEquiv_symm_comp, strictRawModuleTensorConeUnderMap_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceUnderUncurry_yoneda]
  rfl

end SerrePositivity.EInfinity.BarrattEccles
