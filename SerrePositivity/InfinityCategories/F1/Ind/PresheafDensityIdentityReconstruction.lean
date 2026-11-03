module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.Source
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationFiberMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationRestrictionBase
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationValueComparison
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.TwistedSourceElements
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafUnstraightening
public import SerrePositivity.InfinityCategories.F1.Ind.PresheafDensityIdentityValue

/-!
概要：元の恒等点の全 fiber パラメータを、元の評価密度余錐の unstraightening へ持ち上げる。
方針：同じ復元射を恒等点の包含に制限し、元の native fiber 値写像の比較を前合成する。
規約：元の fiber 包含と元の全余錐の像を保持する。
使われ方：Yoneda comma 比較の値写像と元の恒等点評価の同型の中間写像。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F

/-- 元の恒等点の同じ全 fiber を、同じ評価図式の unstraightening に含める。 -/
def presheafDensityIdentityReconstruction :
    (SSet.uliftFunctor.{u + 1, u}).obj (vertexFiber p x) ⟶
      leftUnstraightening (presheafDensityEvaluationDiagram F x) :=
  (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsIdentityInclusion p x) ≫
    presheafDensityEvaluationReconstructionLift F x

/-- この同じ持ち上げの元の底への射影は、元の fiber 包含そのもの。 -/
lemma presheafDensityIdentityReconstruction_projection :
    presheafDensityIdentityReconstruction F x ≫
      leftUnstraighteningProjection (presheafDensityEvaluationDiagram F x) =
    (SSet.uliftFunctor.{u + 1, u}).map (vertexFiberι p x) := by
  rw [presheafDensityIdentityReconstruction, Category.assoc,
    presheafDensityEvaluationReconstructionLift_projection,
    presheafDensityEvaluationSourceBase, ← Functor.map_comp,
    twistedSourceElementsIdentityInclusion_fst]

/-- 同じ native 評価余錐の元の値写像を、同じ恒等点上の全 fiber へ制限する。 -/
def presheafDensityNativeIdentityValue :=
  presheafDensityIdentityReconstruction F x ≫
    F2.coconeFiberValueMapAt (presheafDensityEvaluationCocone F x)
      (presheafDensityEvaluationVertex F x) (presheafDensityEvaluationCocone_vertex F x)

/-- 同じ native 値写像は、元の大域評価の恒等点上の同じ制限と関手同型。 -/
def presheafDensityNativeIdentityValueIso :
    FunctorIso (presheafDensityNativeIdentityValue F x) (presheafDensityIdentityValue F x) := by
  have h := ((presheafDensityEvaluationFiberIso F x).precomp
    (presheafDensityEvaluationReconstructionLift F x)) ≪≫
      presheafDensityEvaluationValueComparisonIso F x
  exact FunctorIso.precomp h
    ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsIdentityInclusion p x))

/-- 元の評価密度余錐から得る同じ恒等点値写像自身が同値。 -/
lemma presheafDensityNativeIdentityValue_isQCatEquivalence :
    IsQCatEquivalence (presheafDensityNativeIdentityValue F x) :=
  (presheafDensityIdentityValue_isQCatEquivalence F x).ofFunctorIso
    (presheafDensityNativeIdentityValueIso F x).symm

end SerrePositivity.InfinityCategories.F2.Ind
