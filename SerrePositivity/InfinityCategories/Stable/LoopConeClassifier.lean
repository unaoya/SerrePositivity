module
public import SerrePositivity.InfinityCategories.Stable.LoopConeFamilyComparison
public import SerrePositivity.InfinityCategories.Stable.SliceSquareDiagramEvaluation
public import SerrePositivity.InfinityCategories.Core.ConeRestrictionCocartesianEdge
public import SerrePositivity.InfinityCategories.F1B.UnitComma
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
/-!
概要：全 loop cospan 上の任意錐から始点比較の comma への実関手。
方針：底を固定した比較を錐頂点で評価し、同じ区間の族を comma へ送る。
規約：二射影を厳密に保持する。同値性は別工程。使われ方：一般安定性判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
lemma loopDiagramConeFamily_apex (X : SSet.{u}) [Quasicategory X] :
    loopDiagramConeFamily X ≫
      (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι ≫
        coneApexEvaluation (horn 2 2 : SSet.{u}) X = loopDiagramEvaluation X 0 0 := by
  rw [← Category.assoc, loopDiagramConeFamily_ι]
  dsimp only [coneApexEvaluation]
  rw [Category.assoc, stable_pre_evaluateFunctorAt]
  have hp := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
    cospanConeSquareIso_initialPoint.{u}
  change cospanConeSquareIso.hom.app (Opposite.op ⦋0⦌)
      ((joinInl (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u})).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = _ at hp
  rw [hp]
  rfl

def loopConeObjects (X : SSet.{u}) [Quasicategory X] : SSet.{u} :=
  pullback (coneRestriction (horn 2 2 : SSet.{u}) X)
    (loopDiagramConeFamily X ≫ limitConeProjection (horn 2 2 : SSet.{u}) X)
abbrev loopConeObjectDiagram (X : SSet.{u}) [Quasicategory X] :
    loopConeObjects X ⟶ (ihom (join (Δ[0] : SSet.{u}) (horn 2 2 : SSet.{u}))).obj X :=
  pullback.fst _ _
abbrev loopConeObjectLoop (X : SSet.{u}) [Quasicategory X] :
    loopConeObjects X ⟶ loopDiagrams X := pullback.snd _ _
def loopConeObjectSource (X : SSet.{u}) [Quasicategory X] : loopConeObjects X ⟶ X :=
  loopConeObjectDiagram X ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X
lemma loopConeComparison_exists (X : SSet.{u}) [Quasicategory X] :
    ∃ H : SSet.Homotopy (loopConeObjectDiagram X)
        (loopConeObjectLoop X ≫ loopDiagramConeFamily X ≫
          (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι),
      H.h ≫ coneRestriction (horn 2 2 : SSet.{u}) X =
        CartesianMonoidalCategory.fst (loopConeObjects X) (Δ[1] : SSet.{u}) ≫
          loopConeObjectDiagram X ≫ coneRestriction (horn 2 2 : SSet.{u}) X := by
  apply loopConeFamilyComparison_exists
  exact pullback.condition
def loopConeComparisonHomotopy (X : SSet.{u}) [Quasicategory X] :
    SSet.Homotopy (loopConeObjectDiagram X)
      (loopConeObjectLoop X ≫ loopDiagramConeFamily X ≫
        (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι) :=
  Classical.choose (loopConeComparison_exists X)
lemma loopConeComparisonHomotopy_over (X : SSet.{u}) [Quasicategory X] :
    (loopConeComparisonHomotopy X).h ≫ coneRestriction (horn 2 2 : SSet.{u}) X =
      CartesianMonoidalCategory.fst (loopConeObjects X) (Δ[1] : SSet.{u}) ≫
        loopConeObjectDiagram X ≫ coneRestriction (horn 2 2 : SSet.{u}) X :=
  Classical.choose_spec (loopConeComparison_exists X)
def loopConeApexComparisonHomotopy (X : SSet.{u}) [Quasicategory X] :
    SSet.Homotopy (loopConeObjectSource X)
      (loopConeObjectLoop X ≫ loopDiagramEvaluation X 0 0) where
  h := (loopConeComparisonHomotopy X).h ≫ coneApexEvaluation (horn 2 2 : SSet.{u}) X
  h₀ := by
    rw [← Category.assoc, (loopConeComparisonHomotopy X).h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, (loopConeComparisonHomotopy X).h₁]
    simp only [Category.assoc, loopDiagramConeFamily_apex]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    exact False.elim z.1.property
def loopConeClassifier (X : SSet.{u}) [Quasicategory X] :
    loopConeObjects X ⟶ unitComma (loopDiagramEvaluation X 0 0) :=
  unitCommaLift (loopDiagramEvaluation X 0 0) (loopConeObjectSource X)
    (loopConeObjectLoop X) (loopConeApexComparisonHomotopy X)
lemma loopConeClassifier_source (X : SSet.{u}) [Quasicategory X] :
    loopConeClassifier X ≫ unitCommaSource (loopDiagramEvaluation X 0 0) =
      loopConeObjectSource X :=
  unitCommaLift_source _ _ _ _
lemma loopConeClassifier_target (X : SSet.{u}) [Quasicategory X] :
    loopConeClassifier X ≫ unitCommaTarget (loopDiagramEvaluation X 0 0) =
      loopConeObjectLoop X :=
  unitCommaLift_target _ _ _ _
def loopConeClassifierSourceFiberMap (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    vertexFiber (loopConeObjectSource X) x ⟶ unitCommaFiber (loopDiagramEvaluation X 0 0) x :=
  vertexFiberMap (loopConeObjectSource X) (unitCommaSource (loopDiagramEvaluation X 0 0))
    (loopConeClassifier X) (loopConeClassifier_source X) x
lemma loopConeClassifierSourceFiberMap_ι (X : SSet.{u}) [Quasicategory X] (x : X _⦋0⦌) :
    loopConeClassifierSourceFiberMap X x ≫
        vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x =
      vertexFiberι (loopConeObjectSource X) x ≫ loopConeClassifier X :=
  vertexFiberMap_ι _ _ _ _ _
lemma loopConeClassifierSourceFiberMap_target (X : SSet.{u}) [Quasicategory X]
    (x : X _⦋0⦌) :
    loopConeClassifierSourceFiberMap X x ≫
        vertexFiberι (unitCommaSource (loopDiagramEvaluation X 0 0)) x ≫
          unitCommaTarget (loopDiagramEvaluation X 0 0) =
      vertexFiberι (loopConeObjectSource X) x ≫ loopConeObjectLoop X := by
  rw [← Category.assoc, loopConeClassifierSourceFiberMap_ι,
    Category.assoc, loopConeClassifier_target]
end SerrePositivity.InfinityCategories
