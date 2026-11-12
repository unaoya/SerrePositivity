module

public import SerrePositivity.HomologicalAlgebra.ChainTotalizationHomotopy
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.QuasiIso
import all SerrePositivity.HomologicalAlgebra.ChainTotalizationHomotopy
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal

/-!
# 非有界単体的複体の正規化実現比較

## 概要
正規化 Moore 複体の直和全複体を、非正規化直和全複体へ同じ包含で自然に比較する。

## 方針
Dold–Kan の鎖ホモトピー同値を、添字延長と非有界全複体ホモトピーの保存で移す。

## 規約
内部次数の有界性は要求しない。比較射は元の Moore 包含の全複体の射である。

## 使われ方
HA 1.2.4、HTT 4.2.4.1。退化成分を殺す native 余錐と具体的な非正規化実現の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicTopology SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A]

/-- 正規化 Moore 複体を用いる、同じ次数規約の直和実現関手。 -/
def normalizedTotalFunctor : SimplicialObject (Complex A) ⥤ Complex A :=
  normalizedMooreComplex (Complex A) ⋙ chainTotalizationFunctor (ModuleCat.{u} A)

/-- 元の正規化 Moore 包含が誘導する、全図式に自然な比較射。 -/
def normalizedTotalComparison : normalizedTotalFunctor A ⟶ directSumTotalFunctor A :=
  Functor.whiskerRight (inclusionOfMooreComplex (Complex A))
    (chainTotalizationFunctor (ModuleCat.{u} A))

/-- 各比較は同じ包含と正規化射影を用いた鎖ホモトピー同値。 -/
def normalizedTotalHomotopyEquiv (X : SimplicialObject (Complex A)) :
    HomotopyEquiv ((normalizedTotalFunctor A).obj X) ((directSumTotalFunctor A).obj X) :=
  chainTotalizationHomotopyEquiv (ModuleCat.{u} A)
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X))

/-- ホモトピー同値の前向きの射は、全関手の同じ自然比較の成分。 -/
theorem normalizedTotalHomotopyEquiv_hom (X : SimplicialObject (Complex A)) :
    (normalizedTotalHomotopyEquiv A X).hom = (normalizedTotalComparison A).app X := rfl

/-- 非有界内部次数でも、元の自然比較は擬同型。 -/
instance normalizedTotalComparison_quasiIso (X : SimplicialObject (Complex A)) :
    QuasiIso ((normalizedTotalComparison A).app X) :=
  inferInstanceAs (QuasiIso (normalizedTotalHomotopyEquiv A X).hom)

/-- 単体的ホモトピーは、同じ実現関手の二つの射の鎖ホモトピーを誘導する。 -/
def directSumTotalHomotopy {X Y : SimplicialObject (Complex A)} {f g : X ⟶ Y}
    (h : SimplicialObject.Homotopy f g) :
    Homotopy ((directSumTotalFunctor A).map f) ((directSumTotalFunctor A).map g) :=
  chainTotalizationHomotopy (ModuleCat.{u} A) h.toChainHomotopy

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
