module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDCompletedCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDPolynomialCech
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 小さい分冪模型の係数変更

## 概要
分冪座標の未完備模型の係数を変更し、各項を p 完備化した厳密な射を得る。

## 方針
余単体の構造射との可換性は未完備模型で示されている。
係数環の下の圏で、標的の係数を制限してこの射を読む。

## 規約
係数の環射は指定した代数構造の構造射。

## 使われ方
BS 著者版 Theorem 6.4 の小さい分冪模型の係数変換。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) (k l : Type u) [CommRing k] [CommRing l] [Algebra k l] (r : ℕ)

local notation "resK" => Under.map (CommRingCat.ofHom (algebraMap k l))

private def coeffOnRings :
    (pdRawModel k r ⋙ Under.forget (CommRingCat.of k)) ⋙ principalCompletionRingFunctor p ⟶
    (pdRawModel l r ⋙ Under.forget (CommRingCat.of l)) ⋙ principalCompletionRingFunctor p :=
  Functor.whiskerRight (pdRawChange k l r) (principalCompletionRingFunctor p)

/-- 小さい完備分冪 Čech 模型の半線形な係数変更。 -/
def pdModelBaseChange : pdModel p k r ⟶ pdModel p l r ⋙ resK where
  app n := Under.homMk ((coeffOnRings p k l r).app n) (by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    let j₁ := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n.len))
    let j₂ := principalCompletionRingCatUnit p (CommRingCat.of (pdRaw l r n.len))
    let f := (pdRawChange k l r).app n
    change ringCatMap p f (j₁ (algebraMap k (pdRaw k r n.len) a)) =
      j₂ (algebraMap l (pdRaw l r n.len) (algebraMap k l a))
    exact (ConcreteCategory.congr_hom (ringCatMap_comp_unit p f) _).trans
      (congrArg j₂ (((pdRawCoefficients k l r n.len).commutes a).trans
        (IsScalarTower.algebraMap_apply k l (pdRaw l r n.len) a))))
  naturality {m n} θ := by
    apply Under.UnderMorphism.ext
    exact (coeffOnRings p k l r).naturality θ

/-- 小さい分冪模型の各項への完備化単位。 -/
def pdModelUnit (n : SimplexCategory) :
    CommRingCat.of (pdRaw k r n.len) ⟶ ((pdModel p k r).obj n).right :=
  principalCompletionRingCatUnit p (CommRingCat.of (pdRaw k r n.len))

/-- 完備化の単位上で、係数変更は未完備の係数変更を延長する。 -/
theorem pdModelBaseChange_unit (n : SimplexCategory) (x : pdRaw k r n.len) :
    ((pdModelBaseChange p k l r).app n).right (pdModelUnit p k r n x) =
      pdModelUnit p l r n (pdRawCoefficients k l r n.len x) :=
  ConcreteCategory.congr_hom (ringCatMap_comp_unit p ((pdRawChange k l r).app n)) x

end SerrePositivity.BhattScholze.Prismatic
