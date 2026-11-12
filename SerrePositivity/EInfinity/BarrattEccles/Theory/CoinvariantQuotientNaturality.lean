module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorTargetCompatibility

/-!
# 指定全複体商と係数射の自然性

HA 3.2.4.7 の自由比較で、指定係数射を全複体の商の前へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {R G : Type u} [CommRing R] [Group G] {K L L' : Complex R}

/-- 指定商は、入力を固定した同変な係数射と厳密に可換する。 -/
lemma coinvariantTotalQuotient_naturality_right (ρ : G →* End K)
    (σ : G →* End L) (τ : G →* End L') (f : L ⟶ L')
    (hf : ∀ g, (σ g).asHom ≫ f = f ≫ (τ g).asHom) :
    coinvariantTotalQuotient ρ σ ≫
      (((Rep.coinvariantsTensor R G).map₂CochainComplex).obj
        (representationCochainComplex ρ)).map (representationCochainMap σ τ f hf) =
    (K ◁ f) ≫ coinvariantTotalQuotient ρ τ := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply mapBifunctor.hom_ext
  intro i j h
  change ιMapBifunctor K L (curriedTensor (ModuleCat R)) (.up ℤ) i j k h ≫
    (coinvariantTotalQuotient ρ σ ≫ mapBifunctorMap (𝟙 (representationCochainComplex ρ))
      (representationCochainMap σ τ f hf) (Rep.coinvariantsTensor R G) (.up ℤ)).f k =
    ιMapBifunctor K L (curriedTensor (ModuleCat R)) (.up ℤ) i j k h ≫
      (mapBifunctorMap (𝟙 K) f (curriedTensor (ModuleCat R)) (.up ℤ) ≫
        coinvariantTotalQuotient ρ τ).f k
  rw [HomologicalComplex.comp_f, ← Category.assoc, coinvariantTotalQuotient_ι,
    Category.assoc, ι_mapBifunctorMap]
  rw [HomologicalComplex.comp_f, ι_mapBifunctorMap_assoc]
  rw [coinvariantTotalQuotient_ι]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

namespace BarrattEccles
open SerrePositivity.TensorPowers
variable (R : Type u) [CommRing R] (X Y : Complex R) (m n : ℕ)

/-- 指定係数比較の順射を二色表示へ接続すると、同じ係数射と左右の指定商になる。 -/
lemma twoColorCoefficientTarget_quotient :
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (twoColorSourceComplexAction R m n) ≫
    (twoColorComplexInputHomotopyEquiv R m n (twoColorSeparatedInput X Y m n)).hom ≫
    (twoColorTargetSchurIso R X Y m n).hom ≫
      ((schurArityInputCoinvariantIso R X m).hom ⊗ₘ
        (schurArityInputCoinvariantIso R Y n).hom) =
    ((power X m ⊗ power Y n) ◁ twoColorCoefficientComparison R m n) ≫
    tensorμ (power X m) (power Y n) ((operad R).arity m) ((operad R).arity n) ≫
      (actionCoinvariantQuotient (tensorComplexAction
        (finiteBijectionComplexAction (bijectionFunctor X) m) (arityComplexAction R m)) ⊗ₘ
       actionCoinvariantQuotient (tensorComplexAction
        (finiteBijectionComplexAction (bijectionFunctor Y) n) (arityComplexAction R n))) := by
  simp only [twoColorComplexInputHomotopyEquiv_hom, twoColorCoefficientCochainMap,
    twoColorInputTotalFunctor, twoColorSeparatedInput]
  erw [reassoc_of% coinvariantTotalQuotient_naturality_right]
  rw [twoColorTargetSchurIso_quotient]

/-- 係数優先の順序でも、指定係数射と元の二つの Schur 商が一致する。 -/
lemma twoColorCoefficientTarget_schurQuotient :
    (β_ ((operad R).arity (m + n)) (power X m ⊗ power Y n)).hom ≫
    coinvariantTotalQuotient
      (tensorComplexAction (twoColorLeftInputAction X m n) (twoColorRightInputAction Y m n))
      (twoColorSourceComplexAction R m n) ≫
    (twoColorComplexInputHomotopyEquiv R m n (twoColorSeparatedInput X Y m n)).hom ≫
      (twoColorTargetSchurIso R X Y m n).hom =
    (twoColorCoefficientComparison R m n ▷ (power X m ⊗ power Y n)) ≫
    tensorμ ((operad R).arity m) ((operad R).arity n) (power X m) (power Y n) ≫
      (arityCoinvariantComplexQuotient (schurDiagram R (sequence R) X) m ⊗ₘ
        arityCoinvariantComplexQuotient (schurDiagram R (sequence R) Y) n) := by
  apply (cancel_mono ((schurArityInputCoinvariantIso R X m).hom ⊗ₘ
    (schurArityInputCoinvariantIso R Y n).hom)).1
  simp only [Category.assoc]
  rw [twoColorCoefficientTarget_quotient, tensorHom_comp_tensorHom]
  rw [schurArityInputCoinvariantIso_quotient, schurArityInputCoinvariantIso_quotient]
  rw [← actionCoinvariantQuotient, ← actionCoinvariantQuotient]
  have h := BraidedCategory.braiding_naturality
    (twoColorCoefficientComparison R m n) (𝟙 (power X m ⊗ power Y n))
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, id_whiskerRight,
    Category.id_comp] at h
  rw [← reassoc_of% h, reassoc_of% tensorμ_braiding, tensorHom_comp_tensorHom]

end BarrattEccles

end SerrePositivity.EInfinity
