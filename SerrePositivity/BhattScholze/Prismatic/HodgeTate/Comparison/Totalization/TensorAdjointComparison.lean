module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.TensorComponents
public import SerrePositivity.HomologicalAlgebra.ProductTotalHomNaturality
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 随伴による標準テンソル–積全複体比較

## 概要
既存の tensor–Hom 随伴と、指定された Hom–Tot 同型から標準の比較鎖写像を作る。

## 方針
随伴の単位を各行へ施し、積全複体を取って Hom–Tot 同型の逆へ合成し、逆転置する。

## 規約
ここでは横次数を整数とする。比較射の可逆性や平坦性を仮定しない。

## 使われ方
BS 著者版 Lemma 4.22 の自然な底変換–Tot 比較の、完備化前の鎖写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R : Type u} [CommRing R]

/-- 固定係数複体とのテンソルを、整数の横次数の各行へ施す。 -/
abbrev tensorRowsInt (L : Complex R) (K : CochainComplex (Complex R) ℤ) :
    CochainComplex (Complex R) ℤ :=
  ((tensorLeft L).mapHomologicalComplex (.up ℤ)).obj K

/-- 随伴の指定された単位を各行へ施した鎖写像。 -/
def tensorUnitRows (L : Complex R) (K : CochainComplex (Complex R) ℤ) :
    K ⟶ ((homFunctor L).mapHomologicalComplex (.up ℤ)).obj (tensorRowsInt L K) where
  f n := (ihom.adjunction L).unit.app (K.X n)
  comm' i j _ := ((ihom.adjunction L).unit.naturality (K.d i j)).symm

/-- 行ごとの単位は、元の二重複体に関して自然である。 -/
@[reassoc] theorem tensorUnitRows_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℤ} (g : K ⟶ M) :
    g ≫ tensorUnitRows L M = tensorUnitRows L K ≫
      ((homFunctor L).mapHomologicalComplex (.up ℤ)).map
        (((tensorLeft L).mapHomologicalComplex (.up ℤ)).map g) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact (ihom.adjunction L).unit.naturality (g.f n)

/-- Hom–Tot の指定同型の逆へ合成した、標準比較の転置。 -/
def tensorTotalTranspose (L : Complex R) (K : CochainComplex (Complex R) ℤ) :
    (ProductTotal.functor (ModuleCat.{u} R)).obj K ⟶
      homComplex R L ((ProductTotal.functor (ModuleCat.{u} R)).obj (tensorRowsInt L K)) :=
  (ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRows L K) ≫
    (ProductTotal.homTotalIso L (tensorRowsInt L K)).inv

/-- 単位と指定 Hom–Tot 比較を逆転置した、標準のテンソル–Tot 鎖写像。 -/
def tensorTotalComparisonInt (L : Complex R) (K : CochainComplex (Complex R) ℤ) :
    cochainTensor L ((ProductTotal.functor (ModuleCat.{u} R)).obj K) ⟶
      (ProductTotal.functor (ModuleCat.{u} R)).obj (tensorRowsInt L K) :=
  (tensorHomEquiv L _ _).symm (tensorTotalTranspose L K)

/-- 標準比較の転置は、構成に用いた単位と指定射影に戻る。 -/
theorem tensorTotalComparisonInt_transpose (L : Complex R) (K : CochainComplex (Complex R) ℤ) :
    tensorHomEquiv L _ _ (tensorTotalComparisonInt L K) = tensorTotalTranspose L K :=
  Equiv.apply_symm_apply _ _

/-- 指定された転置の自然性。 -/
@[reassoc] theorem tensorTotalTranspose_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℤ} (g : K ⟶ M) :
    (ProductTotal.functor (ModuleCat.{u} R)).map g ≫ tensorTotalTranspose L M =
      tensorTotalTranspose L K ≫ homPostcompose L
        ((ProductTotal.functor (ModuleCat.{u} R)).map
          (((tensorLeft L).mapHomologicalComplex (.up ℤ)).map g)) := by
  dsimp only [tensorTotalTranspose]
  rw [← Category.assoc, ← Functor.map_comp, tensorUnitRows_naturality, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun h =>
    (ProductTotal.functor (ModuleCat.{u} R)).map (tensorUnitRows L K) ≫ h)
      ((ProductTotal.homTotalNatIso L).inv.naturality
        (((tensorLeft L).mapHomologicalComplex (.up ℤ)).map g))

/-- 標準の比較鎖写像は、二重複体の射について自然である。 -/
@[reassoc] theorem tensorTotalComparisonInt_naturality (L : Complex R)
    {K M : CochainComplex (Complex R) ℤ} (g : K ⟶ M) :
    cochainTensorMap (𝟙 L) ((ProductTotal.functor (ModuleCat.{u} R)).map g) ≫
        tensorTotalComparisonInt L M =
      tensorTotalComparisonInt L K ≫ (ProductTotal.functor (ModuleCat.{u} R)).map
        (((tensorLeft L).mapHomologicalComplex (.up ℤ)).map g) := by
  apply (tensorHomEquiv L _ _).injective
  change tensorHomEquiv L _ _
    ((L ◁ (ProductTotal.functor (ModuleCat.{u} R)).map g) ≫ tensorTotalComparisonInt L M) = _
  rw [tensorHomEquiv_naturality_source, tensorHomEquiv_naturality_target,
    tensorTotalComparisonInt_transpose, tensorTotalComparisonInt_transpose]
  exact tensorTotalTranspose_naturality L g

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
