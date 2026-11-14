module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramCoefficientEZ
public import SerrePositivity.HomologicalAlgebra.NormalizedEZMap

/-!
概要：係数図式の同値の二つの射を、元の指定係数 AW・shuffle の全図式射と照合する。
方針：指定写像の自然性で自然変換を作り、成分交換と同型の合成を評価する。
規約：図式の射を選び直さず、構成済みの同値の hom・inv を同定する。
使われ方：HA 1.2.4、G10 の元の指定比較との最終照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t r
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {B : Type t} [Category.{r} B] [Abelian B]
variable (F : ModuleCat.{u} ℤ ⥤ B) [F.Additive]
variable (C D : J ⥤ SimplicialObject (ModuleCat.{u} ℤ))

/-- 元の係数 AW の全図式射。 -/
def coefficientEZDiagramAW : coefficientEZSourceDiagram F C D ⟶
    integerEZTargetDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ) where
  app j := mappedNormalizedAlexanderWhitney F (C.obj j) (D.obj j)
  naturality _ _ f := mappedNormalizedAlexanderWhitney_naturality F (C.map f) (D.map f)

/-- 元の係数 shuffle の全図式射。 -/
def coefficientEZDiagramShuffle :
    integerEZTargetDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ) ⟶
      coefficientEZSourceDiagram F C D where
  app j := mappedNormalizedShuffle F (C.obj j) (D.obj j)
  naturality _ _ f := mappedNormalizedShuffle_naturality F (C.map f) (D.map f)

/-- 係数図式同値の順方向は元の指定 AW。 -/
theorem coefficientEZDiagramEquiv_hom : (coefficientEZDiagramEquiv F C D).hom =
    (functorToComplexOfFunctors J B (.down ℕ)).map (coefficientEZDiagramAW F C D) := by
  rfl

/-- 係数図式同値の逆方向は元の指定 shuffle。 -/
theorem coefficientEZDiagramEquiv_inv : (coefficientEZDiagramEquiv F C D).inv =
    (functorToComplexOfFunctors J B (.down ℕ)).map (coefficientEZDiagramShuffle F C D) := by
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
