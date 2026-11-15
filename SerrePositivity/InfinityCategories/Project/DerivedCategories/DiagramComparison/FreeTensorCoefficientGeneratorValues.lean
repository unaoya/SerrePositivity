module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWLastCut

/-!
# 自由正規化生成元のテンソル係数移送

概要：指定係数移送を二つの射影自由生成元の純テンソルで評価する。
方針：既存の斉次包含と係数比較の式を合成する。
規約：IS-W2 B02のAW全切断の成分照合の証明分割。既存比較を保持する。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の自由鎖AWと実合成の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories
open DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A]

/-- 概要：元のMoore射影生成元を負次数へ延長する。
方針：指定extend項同型の逆射。規約：新しい正規化を選ばない。
使われ方：HA 1.2.4 のAW各切断の値の表示。 -/
def freeNegativeGenerator (X : SSet.{u}) (n : ℕ) (x : X.obj (Opposite.op ⦋n⦌)) :
    (freeNegativeChains (A := A) X).X (-(n : ℤ)) :=
  (((normalizedMooreComplex (ModuleCat A)).obj (X ⋙ ModuleCat.free A)).extendXIso
    ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv
      ((DoldKan.PInftyToNormalizedMooreComplex (X ⋙ ModuleCat.free A)).f n
        (ModuleCat.freeMk x))

/-- 概要：同じ係数比較は二因子の射影生成元を対応する負次数純テンソルに送る。
方針：既存の包含公式・係数テンソル公式・自由生成元公式。
規約：任意の二次数。使われ方：HA 1.2.4 のAW全切断の計算。 -/
theorem freeTensorCoefficient_projection_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (i j n : ℕ) (h : i + j = n)
    (x : X.obj (Opposite.op ⦋i⦌)) (y : Y.obj (Opposite.op ⦋j⦌)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X)
    let D := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    (F.map (ιMapBifunctor C D integerTensorBifunctor (.down ℕ) i j n h) ≫
      (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C D)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
        (-(n : ℤ)) ≫
      (tensorIso (integerCoefficientFreeChainsIso φ X)
        (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
      (coefficientUnit φ (integerTensor (C.X i) (D.X j))
        (((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X)).f i
          (integerGenerator x)) ⊗ₜ[ℤ]
         ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y)).f j
          (integerGenerator y)))) =
    ιTensorObj (freeNegativeChains (A := A) X) (freeNegativeChains (A := A) Y)
      (-(i : ℤ)) (-(j : ℤ)) (-(n : ℤ)) (by omega)
      (freeNegativeGenerator X i x ⊗ₜ[A] freeNegativeGenerator Y j y) := by
  dsimp only
  dsimp only [negativeMooreTensorCoefficientIso, Iso.trans_hom,
    tensorIso_hom, Functor.mapIso_hom]
  simp only [comp_f, Category.assoc]
  erw [reassoc_of% (integerNegativeTensorBaseChangeIso_ι φ
    ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))
    ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)) i j n h)]
  rw [DifferentialGraded.ι_tensorHom_assoc, DifferentialGraded.ι_tensorHom]
  simp only [ModuleCat.comp_apply]
  have ht := coefficientUnit_tensorComparison φ
    (((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X)).X i)
    (((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)).X j)
    ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X)).f i (integerGenerator x))
    ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y)).f j (integerGenerator y))
  erw [ht, ModuleCat.MonoidalCategory.tensorHom_tmul]
  erw [freeChainsCoefficient_generator_value φ X i x,
    freeChainsCoefficient_generator_value φ Y j y]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
