module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.ProductChainsCoefficientProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NegativeAWRestriction

/-!
概要：同じraw AWの係数生成元の値から元の自由積AWの成分等式を得る。
方針：係数単位による射の検出、Moore包含による制限、指定項同型の消去を合成する。
規約：IS-W2 B02の既存構成の貼り合わせ。元の射・射影・係数同型を保持する。
使われ方：HA 1.2.4、G10の全単体Hom比較の成分照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory AlgebraicTopology AlgebraicTopology.DoldKan HomologicalComplex
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A] (φ : simplicialRingCoefficient.{u} →+* A)

/-- 元のraw生成元の等式を指定自由積AWの負次数成分へ制限する。 -/
theorem freeProductAlexanderWhitney_f_eq_of_raw (X Y : SSet.{u}) (n : ℕ)
    (T : ModuleCat A)
    (t : (freeNegativeChains (A := A) X ⊗ freeNegativeChains (A := A) Y).X
      (-(n : ℤ)) ⟶ T)
    (h : (freeNegativeChains (A := A) (X ⊗ Y)).X (-(n : ℤ)) ⟶ T)
    (hraw : ∀ x : X.obj (Opposite.op ⦋n⦌), ∀ y : Y.obj (Opposite.op ⦋n⦌),
      ((integerCoefficientExtension φ).map
        ((alexanderWhitney (linearizedSpace X) (linearizedSpace Y)).f n ≫
          (chainIntegerTensorMap (PInftyToNormalizedMooreComplex (linearizedSpace X))
            (PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        ((((integerCoefficientExtension φ).mapHomologicalComplex (.down ℕ)).obj
          (chainIntegerTensor ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace X))
            ((normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)))).extendXIso
              ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace X) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ X)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)) ≫ t)
        (coefficientUnit φ (integerTensor ((linearizedSpace X).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator x ⊗ₜ[ℤ] integerGenerator y)) =
      h (freeNegativeGenerator (X ⊗ Y) n (x, y))) :
    (freeProductAlexanderWhitney φ X Y).f (-(n : ℤ)) ≫ t = h := by
  let F := integerCoefficientExtension φ
  let S := simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y)
  let N := (normalizedMooreComplex (ModuleCat A)).obj (S ⋙ F)
  let row := (N.extendXIso ComplexShape.embeddingDownNat
    (i := n) (i' := -(n : ℤ)) rfl).inv
  let e := integerCoefficientProductChainsIso φ X Y
  let tout := (tensorIso (integerCoefficientFreeChainsIso φ X)
    (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)) ≫ t
  have hn := negativeCoefficientAlexanderWhitney_f_eq_of_raw φ
    (linearizedSpace X) (linearizedSpace Y) n T tout
      (row ≫ e.hom.f (-(n : ℤ)) ≫ h) (by
        apply coefficientUnit_integerTensor_hom_ext φ
          (X.obj (Opposite.op ⦋n⦌)) (Y.obj (Opposite.op ⦋n⦌)) T
        intro x y
        have hg := congrArg (fun z => h z)
          (productChainsCoefficient_generator_value φ X Y n x y)
        exact (hraw x y).trans hg.symm)
  have he : e.hom.f (-(n : ℤ)) ≫ e.inv.f (-(n : ℤ)) = 𝟙 _ := by
    have v := congrArg (fun f => HomologicalComplex.Hom.f f (-(n : ℤ))) e.hom_inv_id
    simpa only [comp_f, id_f] using v
  have ht : e.hom.f (-(n : ℤ)) ≫ (freeProductAlexanderWhitney φ X Y).f (-(n : ℤ)) ≫ t =
      (negativeCoefficientAlexanderWhitney φ (linearizedSpace X) (linearizedSpace Y)).f
        (-(n : ℤ)) ≫ tout := by
    change e.hom.f (-(n : ℤ)) ≫
      (e.inv ≫ negativeCoefficientAlexanderWhitney φ (linearizedSpace X) (linearizedSpace Y) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ X)
          (integerCoefficientFreeChainsIso φ Y)).hom).f (-(n : ℤ)) ≫ t = _
    dsimp only [tout]
    simp only [comp_f, ← Category.assoc]
    rw [he, Category.id_comp]
  apply (cancel_epi (e.hom.f (-(n : ℤ)))).1
  apply (cancel_epi row).1
  rw [ht]
  exact hn

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
