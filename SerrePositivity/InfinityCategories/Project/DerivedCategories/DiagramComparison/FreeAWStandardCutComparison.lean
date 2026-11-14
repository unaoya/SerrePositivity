module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.AWCutFaces
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeProductAWCutValues
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeNegativeStandardHomEvaluation

/-!
概要：同じ各切断の成分等式をraw自由AWと実標準AWの全切断和へまとめる。
方針：指定raw自由AWの生成元評価と実標準AWの逆随伴評価を有限和で合わせる。
規約：各切断の照合条件を明記した既存評価・貼り合わせの法則。
使われ方：HA 1.2.4、IS-W2 B02の実射の成分照合の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open scoped Simplicial TensorProduct
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 各切断で同じ実合成になるtensor射は、raw AWの全切断和でも指定逆随伴と一致。 -/
theorem freeProductAW_standard_raw_value
    (φ : simplicialRingCoefficient.{u} →+* A) (W Y : SSet.{u}) (x y z : D)
    (g : W ⟶ standardHomSpace (R := A) y z)
    (f : Y ⟶ standardHomSpace (R := A) x y)
    (t : freeNegativeChains (A := A) W ⊗ freeNegativeChains (A := A) Y ⟶
      homObject A D x z) (n : ℕ)
    (w : W.obj (Opposite.op ⦋n⦌)) (a : Y.obj (Opposite.op ⦋n⦌))
    (hcut : ∀ c : Fin (n + 1),
      t.f (-(n : ℤ))
        (ιTensorObj (freeNegativeChains (A := A) W) (freeNegativeChains (A := A) Y)
          (-(c.val : ℤ)) (-((n - c.val : ℕ) : ℤ)) (-(n : ℤ))
          (by have := awDegrees n c; omega)
          (freeNegativeGenerator W c.val (W.map (awFront n c).op w) ⊗ₜ[A]
            freeNegativeGenerator Y (n - c.val) (Y.map (awBack n c).op a))) =
        compose A (p := -((n - c.val : ℕ) : ℤ)) (q := -(c.val : ℤ)) (n := -(n : ℤ))
          (standardTopEval (R := A) y z c.val
            (standardPullback (awFront n c).toOrderHom (g.app _ w)))
          (standardTopEval (R := A) x y (n - c.val)
            (standardPullback (awBack n c).toOrderHom (f.app _ a)))
          (by have := c.isLt; omega)) :
    let F := integerCoefficientExtension φ
    let C := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace W)
    let E := (normalizedMooreComplex (ModuleCat ℤ)).obj (linearizedSpace Y)
    let h := (g ⊗ₘ f) ≫ (β_ _ _).hom ≫ standardComposition (R := A) x y z
    t.f (-(n : ℤ))
      ((F.map (alexanderWhitneyApp (linearizedSpace W) (linearizedSpace Y) n ≫
        (chainIntegerTensorMap
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace W))
          (AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex (linearizedSpace Y))).f n) ≫
        (((F.mapHomologicalComplex (.down ℕ)).obj (chainIntegerTensor C E)).extendXIso
          ComplexShape.embeddingDownNat (i := n) (i' := -(n : ℤ)) rfl).inv ≫
        (negativeMooreTensorCoefficientIso φ (linearizedSpace W) (linearizedSpace Y)).hom.f
          (-(n : ℤ)) ≫
        (tensorIso (integerCoefficientFreeChainsIso φ W)
          (integerCoefficientFreeChainsIso φ Y)).hom.f (-(n : ℤ)))
        (coefficientUnit φ (integerTensor ((linearizedSpace W).obj (Opposite.op ⦋n⦌))
          ((linearizedSpace Y).obj (Opposite.op ⦋n⦌)))
            (integerGenerator w ⊗ₜ[ℤ] integerGenerator a))) =
      (((freeNegativeChainsAdjunction A).homEquiv (W ⊗ Y) (homObject A D x z)).symm
        (h ≫ standardDoldKanSpaceMap x z)).f (-(n : ℤ))
          (freeNegativeGenerator (W ⊗ Y) n (w, a)) := by
  dsimp only
  have hw := congrArg (fun b => t.f (-(n : ℤ)) b)
    (freeProductAlexanderWhitney_sum_value φ W Y n w a)
  rw [map_sum] at hw
  refine hw.trans ?_
  rw [freeNegativeStandardAW_generator_eval]
  simp only [Finset.sum_coe_sort_eq_attach, Finset.sum_attach_univ]
  apply Finset.sum_congr rfl
  intro c _
  exact (hcut c).trans (awTerm_univ_top_faces (g.app _ w) (f.app _ a) c).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
