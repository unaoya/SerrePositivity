module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeEZTargetDiagram
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductComparisonNaturality

/-!
概要：自由積の EZ 同値を、任意の単体的集合の二図式について元の自由正規化鎖へ戻す。
方針：積と二因子それぞれの指定自由化同型を全自然同型として用いる。
規約：図式の全射と実鎖ホモトピーを保ち、点ごとの同値に置き換えない。
使われ方：HA 1.2.4、G10 の積重みから正規化テンソルへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {J : Type v} [Category.{w} J] {A : Type u} [CommRing A]
variable (φ : simplicialRingCoefficient.{u} →+* A) (X Y : J ⥤ SSet.{u})

/-- 元の整数自由化を図式に後合成する。 -/
abbrev integerLinearizedSpaceDiagram (X : J ⥤ SSet.{u}) :=
  X ⋙ (SimplicialObject.whiskering _ _).obj integerLinearization

/-- 元の A 自由正規化鎖の複体値図式。 -/
abbrev freeNegativeChainsDiagram (X : J ⥤ SSet.{u}) :=
  X ⋙ (SimplicialObject.whiskering _ _).obj (ModuleCat.free A) ⋙
    normalizedMooreComplex (ModuleCat A) ⋙ ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)

/-- 積側を元の自由積図式へ戻す全自然同型。 -/
def freeProductSourceDiagramIso :
    coefficientEZSourceDiagram (integerCoefficientExtension φ)
      (integerLinearizedSpaceDiagram X) (integerLinearizedSpaceDiagram Y) ⋙
        ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A) ≅
    freeNegativeChainsDiagram (A := A) (X ⊗ Y) :=
  NatIso.ofComponents (fun j => integerCoefficientProductChainsIso φ (X.obj j) (Y.obj j))
    (fun f => integerCoefficientProductChainsIso_naturality φ (X.map f) (Y.map f))

/-- 二因子のテンソル側を元の自由正規化鎖へ戻す全自然同型。 -/
def freeProductTargetDiagramIso :
    negativeEZTargetDiagram φ (integerLinearizedSpaceDiagram X) (integerLinearizedSpaceDiagram Y) ≅
      freeNegativeChainsDiagram (A := A) X ⊗ freeNegativeChainsDiagram (A := A) Y :=
  NatIso.ofComponents (fun j => tensorIso
    (integerCoefficientFreeChainsIso φ (X.obj j)) (integerCoefficientFreeChainsIso φ (Y.obj j)))
    (fun f => integerCoefficientFreeTensorIso_naturality φ (X.map f) (Y.map f))

/-- 二図式についての元の自由積正規化と正規化テンソルの鎖ホモトピー同値。 -/
def freeProductDiagramEZEquiv :
    HomotopyEquiv
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) (X ⊗ Y)))
      ((functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
        (freeNegativeChainsDiagram (A := A) X ⊗ freeNegativeChainsDiagram (A := A) Y)) := by
  let T := functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)
  let e := negativeDiagramExchangeIso
    (coefficientEZSourceDiagram (integerCoefficientExtension φ)
      (integerLinearizedSpaceDiagram X) (integerLinearizedSpaceDiagram Y)) ≪≫
    T.mapIso (freeProductSourceDiagramIso φ X Y)
  exact (HomotopyEquiv.ofIso e.symm).trans
    ((negativeEZDiagramTargetEquiv φ (integerLinearizedSpaceDiagram X)
      (integerLinearizedSpaceDiagram Y)).trans
        (HomotopyEquiv.ofIso (T.mapIso (freeProductTargetDiagramIso φ X Y))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
