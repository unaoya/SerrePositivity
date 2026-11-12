module

public import SerrePositivity.HomologicalAlgebra.FreePresheafFunctor
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
import all SerrePositivity.HomologicalAlgebra.FreePresheafFunctor

/-!
# 表現可能な標準単体の係数付き収縮

## 概要
ULift を含まない表現可能標準単体に増大と extra degeneracy を指定し、係数の余積へ移す。

## 方針
既存の標準単体の収縮を全単体の同型で移し、任意の係数対象の余積関手を適用する。

## 規約
同じ表現可能前層の Hom を添字とする。係数に平坦性や有界性を仮定しない。

## 使われ方
Weibel §2.2、HA 1.2.4。標準単体の線形重みの増大完全性を各評価で確認する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits Opposite
namespace SerrePositivity.HomologicalAlgebra

/-- 元の Hom 集合をそのまま用いた、表現可能標準単体の増大。 -/
def rawSimplexAugmented (k : SimplexCategory) : SimplicialObject.Augmented (Type 0) where
  left := yoneda.obj k
  right := terminal (Type 0)
  hom := { app _ := terminal.from _ }

/-- 標準単体の ULift を全単体で除く、増大を保つ同型。 -/
def standardRawSimplexIso (k : SimplexCategory) :
    SSet.Augmented.stdSimplex.obj k ≅ rawSimplexAugmented k :=
  Comma.isoMk (NatIso.ofComponents (fun _ => Equiv.ulift.toIso) (by intros; rfl))
    (Iso.refl _) (by
      apply NatTrans.ext
      funext n
      exact terminal.hom_ext _ _)

/-- 同じ元の Hom 集合を持つ標準単体の指定 extra degeneracy。 -/
def rawSimplexExtraDegeneracy (k : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (rawSimplexAugmented k) :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso (standardRawSimplexIso k)
    (SSet.Augmented.StandardSimplex.extraDegeneracy k)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C]

/-- 標準単体の各元で指定係数 P の余積を取った、同じ増大単体的対象。 -/
def standardCoefficientAugmented (P : C) (k : SimplexCategory) :
    SimplicialObject.Augmented C :=
  ((SimplicialObject.Augmented.whiskering (Type 0) C).obj (copowerFunctor P)).obj
    (rawSimplexAugmented k)

/-- 係数の余積へ移した、同じ標準単体の指定 extra degeneracy。 -/
def standardCoefficientExtraDegeneracy (P : C) (k : SimplexCategory) :
    SimplicialObject.Augmented.ExtraDegeneracy (standardCoefficientAugmented P k) :=
  (rawSimplexExtraDegeneracy k).map (copowerFunctor P)

/-- 係数付きの標準単体の交代面複体の増大は、同じ増大射を持つ鎖ホモトピー同値。 -/
def standardCoefficientHomotopyEquiv [Preadditive C] [HasZeroObject C]
    (P : C) (k : SimplexCategory) :
    HomotopyEquiv (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (standardCoefficientAugmented P k).left)
      ((ChainComplex.single₀ C).obj (standardCoefficientAugmented P k).right) :=
  (standardCoefficientExtraDegeneracy P k).homotopyEquiv

end SerrePositivity.HomologicalAlgebra
