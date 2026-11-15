module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeTensorCoefficientGeneratorValues

/-!
# 指定自由鎖 Alexander–Whitney の各切断の生成元での値

概要：指定AWの各切断を元の前面・後面の射影生成元で計算する。
方針：既存AW成分と係数テンソルの生成元評価を合成する。
規約：IS-W2 B02の同じ成分照合の証明分割。始域の射影を消したとは仮定しない。
使われ方：HA 1.2.4、Kerodon 2.5（Tag 00ND）の実豊穣合成との照合。
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

/-- 概要：指定AWの一つの切断は同じ前面と後面の自由生成元のテンソル。
方針：AW包含の定義と二つの係数移送の生成元則を適用する。
規約：任意の切断点。使われ方：HA 1.2.4 の自由鎖AWの全切断和。 -/
theorem freeProductAlexanderWhitney_cut_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ) (c : Fin (n + 1))
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X)
    let D := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    (F.map (alexanderWhitneySummand (linearizedSpace X) (linearizedSpace Y) n c ≫
      (chainIntegerTensorMap
        (DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X))
        (DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
      (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C D)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
        (-(n : ℤ)) ≫
      (tensorIso (integerCoefficientFreeChainsIso φ X)
        (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋n⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
        (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
    ιTensorObj (freeNegativeChains (A := A) X) (freeNegativeChains (A := A) Y)
      (-(c.val : ℤ)) (-((n - c.val : ℕ) : ℤ)) (-(n : ℤ))
      (by have := awDegrees n c; omega)
      (freeNegativeGenerator X c.val (X.map (awFront n c).op x) ⊗ₜ[A]
        freeNegativeGenerator Y (n - c.val) (Y.map (awBack n c).op y)) := by
  let F := integerCoefficientExtension φ
  let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X)
  let D := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
  let out :=
    (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C D)).extendXIso
      ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
    (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
      (-(n : ℤ)) ≫
    (tensorIso (integerCoefficientFreeChainsIso φ X)
      (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ))
  change (F.map (_ ≫ _) ≫ out) _ = _
  dsimp only [alexanderWhitneySummand]
  rw [Category.assoc, ι_chainIntegerTensorMap]
  simp only [Functor.map_comp, ModuleCat.comp_apply]
  have hv := coefficientUnit_tensorMap φ
    ((linearizedSpace X).map (awFront n c).op)
    ((linearizedSpace Y).map (awBack n c).op) (integerGenerator x) (integerGenerator y)
  have hx : (linearizedSpace X).map (awFront n c).op (integerGenerator x) =
      integerGenerator (X.map (awFront n c).op x) := integerLinearization_map_generator _ _
  have hy : (linearizedSpace Y).map (awBack n c).op (integerGenerator y) =
      integerGenerator (Y.map (awBack n c).op y) := integerLinearization_map_generator _ _
  rw [hx, hy] at hv
  refine (congrArg (fun t => out (F.map
    (ιMapBifunctor C D integerTensorBifunctor (.down ℕ) c.val (n - c.val) n
      (awDegrees n c)) (F.map (integerTensorMap
        ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X)).f c.val)
        ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (n - c.val))) t)))
    hv).trans ?_
  have hw := coefficientUnit_tensorMap φ
    ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X)).f c.val)
    ((DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y)).f (n - c.val))
    (integerGenerator (X.map (awFront n c).op x))
    (integerGenerator (Y.map (awBack n c).op y))
  refine (congrArg (fun t => out (F.map
    (ιMapBifunctor C D integerTensorBifunctor (.down ℕ) c.val (n - c.val) n
      (awDegrees n c)) t)) hw).trans ?_
  exact freeTensorCoefficient_projection_value φ X Y c.val (n - c.val) n (awDegrees n c)
    (X.map (awFront n c).op x) (Y.map (awBack n c).op y)

/-- 概要：指定AWの全切断和を対応する負次数生成元の和で評価する。
方針：既存の有限和の定義と各切断の式を合成する。
規約：始域は元の整数線形化。使われ方：HA 1.2.4 の指定自由鎖比較の照合。 -/
theorem freeProductAlexanderWhitney_sum_value
    (φ : simplicialRingCoefficient.{u} →+* A) (X Y : SSet.{u})
    (n : ℕ)
    (x : X.obj (Opposite.op ⦋n⦌)) (y : Y.obj (Opposite.op ⦋n⦌)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X)
    let D := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    (F.map (alexanderWhitneyApp (linearizedSpace X) (linearizedSpace Y) n ≫
      (chainIntegerTensorMap
        (DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace X))
        (DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
      (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C D)).extendXIso
        ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
      (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
        (-(n : ℤ)) ≫
      (tensorIso (integerCoefficientFreeChainsIso φ X)
        (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
      (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋n⦌))
        ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
        (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
    ∑ c : Fin (n + 1),
      ιTensorObj (freeNegativeChains (A := A) X) (freeNegativeChains (A := A) Y)
      (-(c.val : ℤ)) (-((n - c.val : ℕ) : ℤ)) (-(n : ℤ))
      (by have := awDegrees n c; omega)
      (freeNegativeGenerator X c.val (X.map (awFront n c).op x) ⊗ₜ[A]
        freeNegativeGenerator Y (n - c.val) (Y.map (awBack n c).op y)) := by
  dsimp only
  simp only [alexanderWhitneyApp, Preadditive.sum_comp, Functor.map_sum,
    ModuleCat.hom_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c _
  exact freeProductAlexanderWhitney_cut_value φ X Y n c x y

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
