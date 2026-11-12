module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDifferential
public import SerrePositivity.HomologicalAlgebra.NormalizedEZMap
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
概要：整数 EZ ホモトピーを一般係数環の負次数正規化テンソルへ接続する。
方針：指定 Moore 比較と整数テンソルの底変換同型で元の AW・shuffle を移す。
規約：元の射と鎖ホモトピーを保持し、平坦性と宇宙の縮小を要求しない。
使われ方：HA 1.2.4、G10 の正規化テンソル／積重み比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- 同宇宙の整数係数環を経由する実係数拡大関手。 -/
abbrev integerCoefficientExtension := integerCoefficientModuleFunctor ⋙ ModuleCat.extendScalars φ

/-- 移した整数テンソルを、移した単体的対象の元の Moore テンソルへ戻す同型。 -/
def negativeMooreTensorCoefficientIso :
    (((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
      (chainIntegerTensor ((normalizedMooreComplex _).obj C)
        ((normalizedMooreComplex _).obj D))).extend ComplexShape.embeddingDownNat ≅
    HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat) :=
  integerNegativeTensorBaseChangeIso ((normalizedMooreComplex _).obj C)
    ((normalizedMooreComplex _).obj D) φ ≪≫
  tensorIso
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
      (normalizedMooreMapIso (integerCoefficientExtension φ) C))
    ((ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
      (normalizedMooreMapIso (integerCoefficientExtension φ) D))

/-- 同じ AW を一般係数の負次数正規化テンソルへの射として表す。 -/
def negativeCoefficientAlexanderWhitney :
    (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).extend
      ComplexShape.embeddingDownNat) ⟶
    HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat) :=
  extendMap (mappedNormalizedAlexanderWhitney (integerCoefficientExtension φ) C D)
    ComplexShape.embeddingDownNat ≫ (negativeMooreTensorCoefficientIso φ C D).hom

/-- 同じ shuffle を一般係数の負次数正規化テンソルからの射として表す。 -/
def negativeCoefficientShuffle :
    HomologicalComplex.tensorObj
      (((normalizedMooreComplex (ModuleCat A)).obj (C ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat)
      (((normalizedMooreComplex (ModuleCat A)).obj (D ⋙ integerCoefficientExtension φ)).extend
        ComplexShape.embeddingDownNat) ⟶ (((normalizedMooreComplex (ModuleCat A)).obj
      (simplicialIntegerTensor C D ⋙ integerCoefficientExtension φ)).extend
      ComplexShape.embeddingDownNat) :=
  (negativeMooreTensorCoefficientIso φ C D).inv ≫
    extendMap (mappedNormalizedShuffle (integerCoefficientExtension φ) C D)
      ComplexShape.embeddingDownNat

/-- 一般係数の負次数模型でも指定 AW→shuffle は恒等と鎖ホモトピック。 -/
def negativeCoefficientEZHomotopy :
    Homotopy (𝟙 _) (negativeCoefficientAlexanderWhitney φ C D ≫
      negativeCoefficientShuffle φ C D) := by
  let h := (mappedNormalizedEZHomotopy (integerCoefficientExtension φ) C D).extend
    ComplexShape.embeddingDownNat
  refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
  · change 𝟙 _ = extendMap (𝟙 _) ComplexShape.embeddingDownNat
    simp
  · dsimp only [negativeCoefficientAlexanderWhitney, negativeCoefficientShuffle]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).map_comp _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
