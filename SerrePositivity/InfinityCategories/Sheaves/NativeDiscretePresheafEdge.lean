module

public import SerrePositivity.InfinityCategories.Sheaves.PresheafYonedaShapeIso
public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalDiagramRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointedTransformationPointHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：元の離散前層の辺を固定図式形状で書き、各点の評価を指定の自然変換と照合する。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Sheaves

/-- 離散前層の包含が送る辺を、指定した両端で表す。 -/
def normalizedDiscreteEdge
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    (PresheafCat C SpaceInfinity.{u}).Edge (functorVertex (discretePresheaf P))
      (functorVertex (discretePresheaf Q)) :=
  ((nerve.edgeMk φ).map (discretePresheafInclusion C).val).ofEq
    ((discretePresheafInclusion C).property.1 P) ((discretePresheafInclusion C).property.1 Q)

def nativeDiscreteEdge
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let U := SSet.uliftFunctor.{u + 1, u}
    let i := nerveOppositeIso (C := C)
    let F := U.map i.hom ≫ discretePresheaf P
    let G := U.map i.hom ≫ discretePresheaf Q
    (PresheafInfinity (nerve C)).Edge (functorVertex F) (functorVertex G) := by
  intro U i F G
  let j := (fixedPresheafShapeIso C).inv
  have hP : j.app _ (functorVertex (discretePresheaf P)) = functorVertex F :=
    functorVertex_precomposition (U.map i.hom) (discretePresheaf P)
  have hQ : j.app _ (functorVertex (discretePresheaf Q)) = functorVertex G :=
    functorVertex_precomposition (U.map i.hom) (discretePresheaf Q)
  exact ((normalizedDiscreteEdge φ).map j).ofEq hP hQ

/-- 元の離散前層の辺を固定図式形状で書き、各点の評価を指定の自然変換と照合する。
Kerodon §8.3 の関手評価。HTT 5.1.5.6 の比較に使う離散前層の辺。 -/
lemma nativeDiscreteEdge_evaluation_hom
    {C : Type u} [SmallCategory C] {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q)
    (x : (nerve C).op _⦋0⦌) :
    let i := nerveOppositeIso (C := C)
    Truncated.HomotopyCategory.homMk (functorEdgeAt (nativeDiscreteEdge φ)
      (ULift.up x)).toTruncated =
      functorHomEvaluate (discretePresheafHom φ) (ULift.up (i.hom.app _ x)) := by
  intro i
  let U := SSet.uliftFunctor.{u + 1, u}
  let j := (fixedPresheafShapeIso C).inv
  let y : (U.obj (nerve Cᵒᵖ)) _⦋0⦌ := ULift.up (i.hom.app _ x)
  have hEq : j ≫ evaluateFunctorAt (Y := SpaceInfinity.{u})
      (X := U.obj (nerve C).op) (ULift.up x) =
      evaluateFunctorAt (Y := SpaceInfinity.{u}) y :=
    evaluateFunctorAt_precomp (U.map i.hom) (ULift.up x)
  rw [show discretePresheafHom φ =
      Truncated.HomotopyCategory.homMk (normalizedDiscreteEdge φ).toTruncated from rfl]
  erw [functorHomEvaluate_edge_hom (normalizedDiscreteEdge φ) y]
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  change (j ≫ evaluateFunctorAt (Y := SpaceInfinity.{u})
      (X := U.obj (nerve C).op) (ULift.up x)).app (Opposite.op ⦋1⦌)
        (normalizedDiscreteEdge φ).edge = _
  rw [hEq]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
