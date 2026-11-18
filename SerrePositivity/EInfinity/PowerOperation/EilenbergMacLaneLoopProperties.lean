module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLanePointedLimits
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneAdjointSuspension
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneFibration
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneQuasiIso
public import SerrePositivity.KST.Spectra.PostMappingFibration
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism

/-!
# シフトした Γ の loop の極限・fibration・準同型

DAG XIII §2.2 の Ω 比較への前段。構成済みの円からの基点付き内部 Hom を使い、
零基点と指定射を保持したまま cone の図式を比較できる形にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

open
  SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes in
instance gammaLoopKan (M : Complex A) : SSet.KanComplex ((gammaLoopFunctor A).obj M).right :=
  PointedMapping.basedHom_kanComplex
    PointedSimplicialSet.circle.{u} (gammaPointed A (M⟦(1 : ℤ)⟧))

lemma gammaLoopFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (gammaLoopFunctor A) := by
  have := gammaPointedFunctor_preservesFiniteLimits A
  have : (PointedSimplicialSet.internalHomFunctor PointedSimplicialSet.circle.{u}).IsRightAdjoint :=
    (PointedSimplicialSet.smashHomAdjunction PointedSimplicialSet.circle.{u}).isRightAdjoint
  dsimp only [gammaLoopFunctor]
  infer_instance

lemma gammaLoopFunctor_preservesZeroMorphisms :
    (gammaLoopFunctor A).PreservesZeroMorphisms := by
  have := gammaLoopFunctor_preservesFiniteLimits A
  infer_instance

open SSet.modelCategoryQuillen in
lemma gammaLoopMap_fibration {M N : Complex A} (p : M ⟶ N)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) : Fibration ((gammaLoopFunctor A).map p).right := by
  have hs : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A (p⟦(1 : ℤ)⟧') := by
    intro n
    exact hp (n + 1)
  have : Fibration (((gammaPointedFunctor A).map (p⟦(1 : ℤ)⟧')).right) :=
    gammaMap_fibration A _ hs
  change Fibration (PointedObject.basedHomMap PointedSimplicialSet.circle.{u}
    ((gammaPointedFunctor A).map (p⟦(1 : ℤ)⟧'))).right
  infer_instance

lemma gammaLoopMap_kanPiIsomorphism {M N : Complex A} (p : M ⟶ N) [QuasiIso p] :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((gammaLoopFunctor A).map p).right :=
  KST.Spectra.PointedMapping.post_piIsomorphism PointedSimplicialSet.circle.{u}
    ((gammaPointedFunctor A).map (p⟦(1 : ℤ)⟧'))
    (gammaMap_kanPiIsomorphism (p⟦(1 : ℤ)⟧'))

end SerrePositivity.EInfinity.PowerOperation
