module
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConePrism
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：元の全 cone prism を同じ定値先端から元の frame 図式への関手の射にする。
方針：区間因子の順を戻した元の全ホモトピーと、その同じ関手辺の類を使う。
規約：元の全区間族と両端を保持する。使われ方：同じ実屋根との大域三角形の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

private lemma conePrismEndpointZero {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₀ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ p := by
  rw [← Category.assoc]
  rfl

private lemma conePrismEndpointOne {K T : SSet.{u + 1}}
    (p : (Δ[1] : SSet.{u + 1}) ⊗ K ⟶ T) :
    SSet.ι₁ (X := K) ≫ ((β_ K (Δ[1] : SSet.{u + 1})).hom ≫ p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ p := by
  rw [← Category.assoc]
  rfl

def strictRawModuleTensorConeHomotopy :
    SSet.Homotopy (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q) where
  h := (β_ (nerve (strictRawModuleTensorElementIndex A X P Q)) (Δ[1] : SSet.{u + 1})).hom ≫
    strictRawModuleTensorConePrism A X P Q
  h₀ := by
    exact (conePrismEndpointZero (strictRawModuleTensorConePrism A X P Q)).trans
      (strictRawModuleTensorConePrism_zero A X P Q)
  h₁ := by
    exact (conePrismEndpointOne (strictRawModuleTensorConePrism A X P Q)).trans
      (strictRawModuleTensorConePrism_one A X P Q)
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property

def strictRawModuleTensorConeFamilyHom :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))).symm (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))))
      (strictRawModuleTensorElementNerveDiagram A X P Q) :=
  SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (strictRawModuleTensorConeHomotopy A X P Q))

end SerrePositivity.EInfinity.BarrattEccles
