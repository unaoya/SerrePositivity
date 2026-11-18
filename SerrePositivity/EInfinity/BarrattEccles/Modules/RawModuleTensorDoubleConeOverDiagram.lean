module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorDoubleConeJoin

/-!
概要：slice 内の大域二重 cone の通常図式と、元の frame 図式への射影を回収する。
方針：元の恒等錐の点評価と、二つの大域射影の厳密な一致を使う。
規約：HA Construction 1.3.1.6・1.3.1.13、同じ全図式を保つ。使われ方：slice prism の両端と全底円柱。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.EInfinity.Modules _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

lemma strictRawModuleTensorIdentityOverPoint_vertex :
    (strictRawModuleTensorIdentityOverPoint A X P).app (Opposite.op ⦋0⦌)
      (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.sliceIdentityCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))) := by
  have hp : SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})) := by
    apply SSet.stdSimplex.ext
    intro i
    apply Fin.ext
    omega
  rw [hp]
  exact SSet.yonedaEquiv_symm_app_id _

def strictRawModuleTensorDoubleConeOverDiagram : nerve (strictRawModuleTensorElementIndex A X P Q) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (strictRawModuleTensorConePoint A X P) :=
  strictRawModuleTensorDoubleConeUnderOverMap A X P Q ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (strictRawModuleTensorIdentityOverPoint A X P)

lemma strictRawModuleTensorDoubleConeOverJoin_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u + 1}) (nerve (strictRawModuleTensorElementIndex A X P Q)) ≫
      strictRawModuleTensorDoubleConeOverJoin A X P Q = strictRawModuleTensorDoubleConeOverDiagram A X P Q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection (strictRawModuleTensorDoubleConeUnderOverMap A X P Q)

lemma strictRawModuleTensorDoubleConeOverDiagram_projection :
    strictRawModuleTensorDoubleConeOverDiagram A X P Q ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (strictRawModuleTensorConePoint A X P) =
        strictRawModuleTensorElementNerveDiagram A X P Q := by
  rw [← strictRawModuleTensorDoubleConeOverJoin_inr, Category.assoc,
    strictRawModuleTensorDoubleConeOverJoin_projection, strictRawModuleTensorConeJoin_inr]

end SerrePositivity.EInfinity.BarrattEccles
