module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.DiagramIntegerEZ
public import SerrePositivity.HomologicalAlgebra.NormalizedMooreMap
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
概要：指定 EZ の図式全体の同値を加法的な係数変更へ運び、元の Moore 正規化へ戻す。
方針：図式への後合成と mapHomotopyEquiv、Moore の全自然同型、同じ負次数延長を使う。
規約：図式の全射と両方向のホモトピーを保持し、平坦性を要求しない。
使われ方：HA 1.2.4、G10 の一般係数の積重みとテンソルの比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t r
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {B : Type t} [Category.{r} B] [Abelian B]
variable (F : ModuleCat.{u} ℤ ⥤ B) [F.Additive]
variable (C D : J ⥤ SimplicialObject (ModuleCat.{u} ℤ))

/-- 積の係数変更後に元の Moore 正規化を取った図式。 -/
abbrev coefficientEZSourceDiagram :=
  simplicialIntegerTensorDiagram C D ⋙
    (SimplicialObject.whiskering (ModuleCat.{u} ℤ) B).obj F ⋙ normalizedMooreComplex B

/-- 積側の係数変更と Moore 正規化を交換する全自然同型。 -/
def coefficientEZSourceIso :
    integerEZSourceDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ) ≅
      coefficientEZSourceDiagram F C D :=
  Functor.isoWhiskerLeft (simplicialIntegerTensorDiagram C D) (normalizedMooreMapNatIso F)

/-- 図式圏の指定整数同値の加法関手による像。 -/
def mappedIntegerEZDiagramEquiv :
    HomotopyEquiv
      ((functorToComplexOfFunctors J B (.down ℕ)).obj
        (integerEZSourceDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ)))
      ((functorToComplexOfFunctors J B (.down ℕ)).obj
        (integerEZTargetDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ))) :=
  ((Functor.whiskeringRight J (ModuleCat.{u} ℤ) B).obj F).mapHomotopyEquiv
    (integerEZDiagramEquiv C D)

/-- 積側を係数変更後の元の正規化へ戻した図式圏の同値。 -/
def coefficientEZDiagramEquiv :
    HomotopyEquiv
      ((functorToComplexOfFunctors J B (.down ℕ)).obj (coefficientEZSourceDiagram F C D))
      ((functorToComplexOfFunctors J B (.down ℕ)).obj
        (integerEZTargetDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ))) :=
  (HomotopyEquiv.ofIso ((functorToComplexOfFunctors J B (.down ℕ)).mapIso
    (coefficientEZSourceIso F C D)).symm).trans (mappedIntegerEZDiagramEquiv F C D)

/-- 同じ比較を負次数へ延長した図式圏の同値。 -/
def negativeCoefficientEZDiagramEquiv :
    HomotopyEquiv
      (((functorToComplexOfFunctors J B (.down ℕ)).obj
        (coefficientEZSourceDiagram F C D)).extend ComplexShape.embeddingDownNat)
      (((functorToComplexOfFunctors J B (.down ℕ)).obj
        (integerEZTargetDiagram C D ⋙ F.mapHomologicalComplex (.down ℕ))).extend
          ComplexShape.embeddingDownNat) := by
  let h := coefficientEZDiagramEquiv F C D
  exact {
    hom := extendMap h.hom ComplexShape.embeddingDownNat
    inv := extendMap h.inv ComplexShape.embeddingDownNat
    homotopyHomInvId := by
      simpa only [extendMap_comp, extendMap_id] using
        h.homotopyHomInvId.extend ComplexShape.embeddingDownNat
    homotopyInvHomId := by
      simpa only [extendMap_comp, extendMap_id] using
        h.homotopyInvHomId.extend ComplexShape.embeddingDownNat }

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
