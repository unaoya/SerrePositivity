module
public import SerrePositivity.HomologicalAlgebra.PointwiseNormalizedMoore
public import SerrePositivity.HomologicalAlgebra.PointwiseExtendComplex
public import SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightFree
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductFrames
/-!
概要：元の正規化線形重みを同じ自由負鎖図式へ全添字で移す。
方針：指定自由係数比較・点ごとのMoore比較・零延長比較を合成する。
規約：IS-W2 A12の係数重み照合の証明分割。同じ包含・射影・生成元を保つ。
使われ方：HA 1.2.4、元の正規化BK Homから指定自由重み比較への接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] {J : Type v} [Category.{w} J]
variable (W : J ⥤ SSet.{0})
/-- 自由線形化を図式圏で正規化したものと、同じ自由鎖図式との指定同型。 -/
def freeLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) := by
  let L := (normalizedMooreComplex (J ⥤ ModuleCat A)).obj (freeLinearizedSimplicialWeight A W.flip)
  let K := L.extend ComplexShape.embeddingDownNat
  have h : complexOfFunctorsToFunctorToComplex.obj K ≅
      freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0}) :=
    (pointwiseExtendIso J (ModuleCat A) ComplexShape.embeddingDownNat).app L ≪≫
      Functor.isoWhiskerRight ((pointwiseMooreIso J (ModuleCat A)).app
        (freeLinearizedSimplicialWeight A W.flip))
        (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A))
  exact (functorComplexExchangeCounitIso J (ModuleCat A) (.up ℤ)).symm.app K ≪≫
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).mapIso h
/-- 元の指定係数余積重みから同じ自由鎖図式への比較。 -/
def normalizedLinearWeightDiagramIso :
    (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W.flip)).extend
      ComplexShape.embeddingDownNat) ≅
    (functorToComplexOfFunctors J (ModuleCat A) (.up ℤ)).obj
      (freeNegativeChainsDiagram (A := A) (W ⋙ SSet.uliftFunctor.{u,0})) :=
  normalizedLinearWeightFreeIso A W.flip ≪≫ freeLinearWeightDiagramIso A W
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
