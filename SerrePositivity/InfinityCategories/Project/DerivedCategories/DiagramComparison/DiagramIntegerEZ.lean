module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ShuffleAWHomotopyNaturality
public import SerrePositivity.HomologicalAlgebra.PointwiseChainHomotopy
public import SerrePositivity.HomologicalAlgebra.FunctorComplexExchange

/-!
概要：指定整数 EZ 比較を任意の添字圏の図式全体の鎖ホモトピー同値へまとめる。
方針：元の積・テンソル・AW・shuffle を図式化し、両方向の自然なホモトピーを使う。
規約：点ごとの同値の存在に置き換えず、指定射とホモトピー成分を保持する。
使われ方：HA 1.2.4、G10 の重みの図式方向と係数変更の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J]
variable (C D : J ⥤ SimplicialObject (ModuleCat.{u} ℤ))

/-- 二図式の次数ごとの整数テンソル。 -/
def simplicialIntegerTensorDiagram : J ⥤ SimplicialObject (ModuleCat.{u} ℤ) where
  obj j := simplicialIntegerTensor (C.obj j) (D.obj j)
  map f := simplicialIntegerTensorMap (C.map f) (D.map f)
  map_id j := by
    apply NatTrans.ext
    funext n
    simp only [CategoryTheory.Functor.map_id]
    exact integerTensorMap_id _ _
  map_comp f g := by
    apply NatTrans.ext
    funext n
    simp only [CategoryTheory.Functor.map_comp]
    exact integerTensorMap_comp _ _ _ _

/-- 積を正規化した複体値図式。 -/
abbrev integerEZSourceDiagram := simplicialIntegerTensorDiagram C D ⋙ normalizedMooreComplex _

/-- 二つの正規化鎖の全テンソルの複体値図式。 -/
def integerEZTargetDiagram : J ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ where
  obj j := chainIntegerTensor ((normalizedMooreComplex _).obj (C.obj j))
    ((normalizedMooreComplex _).obj (D.obj j))
  map f := chainIntegerTensorMap ((normalizedMooreComplex _).map (C.map f))
    ((normalizedMooreComplex _).map (D.map f))
  map_id j := by
    simp only [CategoryTheory.Functor.map_id]
    exact chainIntegerTensorMap_id _ _
  map_comp f g := by
    simp only [CategoryTheory.Functor.map_comp]
    exact chainIntegerTensorMap_comp _ _ _ _

/-- 指定 AW の図式全体の射。 -/
def integerEZDiagramAW : integerEZSourceDiagram C D ⟶ integerEZTargetDiagram C D where
  app j := normalizedAlexanderWhitney (C.obj j) (D.obj j)
  naturality _ _ f := normalizedAlexanderWhitney_naturality (C.map f) (D.map f)

/-- 指定 shuffle の図式全体の射。 -/
def integerEZDiagramShuffle : integerEZTargetDiagram C D ⟶ integerEZSourceDiagram C D where
  app j := normalizedShuffle (C.obj j) (D.obj j)
  naturality _ _ f := normalizedShuffle_naturality (C.map f) (D.map f)

/-- 指定比較は図式圏で両方向の鎖ホモトピー同値を与える。 -/
def integerEZDiagramEquiv :
    HomotopyEquiv
      ((functorToComplexOfFunctors J (ModuleCat.{u} ℤ) (.down ℕ)).obj (integerEZSourceDiagram C D))
      ((functorToComplexOfFunctors J (ModuleCat.{u} ℤ) (.down ℕ)).obj (integerEZTargetDiagram C D)) where
  hom := (functorToComplexOfFunctors J (ModuleCat.{u} ℤ) (.down ℕ)).map (integerEZDiagramAW C D)
  inv := (functorToComplexOfFunctors J (ModuleCat.{u} ℤ) (.down ℕ)).map (integerEZDiagramShuffle C D)
  homotopyHomInvId := pointwiseChainHomotopy
    (fun j => (normalizedEZHomotopy (C.obj j) (D.obj j)).symm)
    (fun f i => (SerrePositivity.KST.ProExcision.ChainHomotopySquare.symm
      (SerrePositivity.KST.ProExcision.normalizedEZHomotopy_square (C.map f) (D.map f))) i)
  homotopyInvHomId := pointwiseChainHomotopy
    (fun j => normalizedShuffleAWHomotopy (C.obj j) (D.obj j))
    (fun f i => normalizedShuffleAWHomotopy_square (C.map f) (D.map f) i)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
