module

public import SerrePositivity.Spectra.Stable.LocalizingMaps
public import SerrePositivity.HomotopicalAlgebra.Monoidal.CofibrantTensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ChosenMapComparison

/-! # Cofibrant endpoints of the actual stabilization arrows

The arrows themselves are not assumed to be cofibrations. Their endpoints
are cofibrant because F_n is left Quillen and K and the chosen test objects
are cofibrant. A supplied replacement produces the requested Q(A) version.
-/

@[expose] public section
universe t v u
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C]
  [ModelCategory C] [Quillen.IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)]

lemma localizingMap_endpoints_cofibrant (n : ℕ) (A : C) [IsCofibrant A] :
    IsCofibrant ((freeAt (K := K) (n + 1)).obj (A ⊗ K)) ∧
      IsCofibrant ((freeAt (K := K) n).obj A) := by
  have := Quillen.tensor_isCofibrant A K
  have := (freeAtAdjunction (K := K) (n + 1)).isLeftAdjoint
  have := (freeAtAdjunction (K := K) n).isLeftAdjoint
  exact ⟨Quillen.map_isCofibrant _ _, Quillen.map_isCofibrant _ _⟩

lemma localizingMaps_endpoints_cofibrant {ι : Type t} (A : ι → C)
    [∀ i, IsCofibrant (A i)] {X Y : GeneralSymmetricSpectrum C K} (f : X ⟶ Y)
    (hf : localizingMaps K A f) : IsCofibrant X ∧ IsCofibrant Y := by
  cases hf with
  | mk p => exact localizingMap_endpoints_cofibrant K p.1 (A p.2)

lemma replacedLocalizingMaps_endpoints_cofibrant {ι : Type t} (A : ι → C)
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    {X Y : GeneralSymmetricSpectrum C K} (f : X ⟶ Y)
    (hf : localizingMaps K (fun i ↦ (cofibrantSource cof).obj (A i)) f) :
    IsCofibrant X ∧ IsCofibrant Y := by
  have := fun i ↦ cofibrantSource_isCofibrant cof (A i)
  exact localizingMaps_endpoints_cofibrant K _ f hf

end SerrePositivity.SpectrumStabilization
