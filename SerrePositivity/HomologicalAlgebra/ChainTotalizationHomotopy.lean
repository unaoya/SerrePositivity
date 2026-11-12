module

public import SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import all SerrePositivity.HomologicalAlgebra.TotalHorizontalHomotopy

/-!
# 非有界な複体を値に持つ鎖複体の直和全複体

## 概要
外側の非負鎖次数を負の余鎖次数に移し、直和全複体を取る関手を構成する。

## 方針
添字延長によるホモトピーの保存と、横ホモトピーの全複体への移送を合成する。

## 規約
内部次数は任意の整数。外側の次数 n の全次数への寄与は -n である。

## 使われ方
HA 1.2.4、Weibel §1.2。単体的複体の正規化・増大の比較を同じ射で全複体へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasCoproducts.{0} C]

/-- 内部次数が非有界の複体の鎖複体を、n↦-n の規約で直和全複体へ送る。 -/
def chainTotalizationFunctor :
    ChainComplex (CochainComplex C ℤ) ℕ ⥤ CochainComplex C ℤ :=
  (ComplexShape.embeddingUpIntLE 0).extendFunctor (CochainComplex C ℤ) ⋙
    HomologicalComplex₂.totalFunctor C (.up ℤ) (.up ℤ) (.up ℤ)

/-- 元の鎖ホモトピーを、同じ二射の直和全複体のホモトピーへ移す。 -/
def chainTotalizationHomotopy
    {K L : ChainComplex (CochainComplex C ℤ) ℕ} {f g : K ⟶ L}
    (h : Homotopy f g) :
    Homotopy ((chainTotalizationFunctor C).map f) ((chainTotalizationFunctor C).map g) :=
  totalHorizontalHomotopy (h.extend (ComplexShape.embeddingUpIntLE 0))

/-- 外側の鎖ホモトピー同値は内部の有界性なしに全複体のホモトピー同値を誘導する。 -/
def chainTotalizationHomotopyEquiv
    {K L : ChainComplex (CochainComplex C ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv ((chainTotalizationFunctor C).obj K)
      ((chainTotalizationFunctor C).obj L) where
  hom := (chainTotalizationFunctor C).map e.hom
  inv := (chainTotalizationFunctor C).map e.inv
  homotopyHomInvId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      chainTotalizationHomotopy C e.homotopyHomInvId
  homotopyInvHomId := by
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using
      chainTotalizationHomotopy C e.homotopyInvHomId

end SerrePositivity.HomologicalAlgebra
