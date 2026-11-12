module

public import SerrePositivity.Spectra.Stable.FrameLocality
public import SerrePositivity.Spectra.Stable.Omega
public import SerrePositivity.HomotopicalAlgebra.Localization.ResolutionHomGenerators
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion

/-! # Ordinary stabilization locality detects the original Omega condition

The detecting family is tested by actual resolution Hom in C. Its existence
for a combinatorial source is proved in the shared layer. The spectral target
replacement is removed, on fibrant spectra, by its actual weak unit and Brown
preservation for evaluation. No stable model structure is used.
-/

@[expose] public section
universe t v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.Reedy

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [ModelCategory C]
  [Quillen.IsQuillenBifunctor (curriedTensor C)] (K : C) [IsCofibrant K]
  [ModelCategory (GeneralSymmetricSpectrum C K)]
  [∀ n : ℕ, Quillen.IsLeftQuillen (freeAt (K := K) n)] [ModelCategory SSet.{v}]
  (cofC : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (cofSp : MorphismProperty.FunctorialFactorizationData
    (cofibrations (GeneralSymmetricSpectrum C K))
    (trivialFibrations (GeneralSymmetricSpectrum C K)))
  (fibSp : MorphismProperty.FunctorialFactorizationData
    (trivialCofibrations (GeneralSymmetricSpectrum C K))
    (fibrations (GeneralSymmetricSpectrum C K)))
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {ι : Type t} (G : ι → C) [∀ i, IsCofibrant (G i)]
  (hdetect : ∀ {Y Z : C} [IsFibrant Y] [IsFibrant Z] (f : Y ⟶ Z),
    weakEquivalences C f ↔ ∀ i, weakEquivalences SSet.{v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily cofC).obj.obj (G i))).map f))

omit [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]
  [ModelCategory SSet.{v}] in
lemma fibrant_levels (E : GeneralSymmetricSpectrum C K) [IsFibrant E] (n : ℕ) :
    IsFibrant (level E n) := by
  have := (freeAtAdjunction (K := K) n).isRightAdjoint
  have := Quillen.isRightQuillen_of_isLeftQuillen (freeAtAdjunction (K := K) n)
  exact Quillen.isFibrant_obj (evaluation (K := K) n) E

include hcof hdetect in
lemma localObjects_iff_replacement_omega (E : GeneralSymmetricSpectrum C K) :
    Bousfield.localObjects cofSp fibSp (localizingMaps K G) E ↔
      IsOmegaSpectrum ((fibrantTarget fibSp).obj E) := by
  let R := (fibrantTarget fibSp).obj E
  have : IsFibrant R := fibrantTarget_isFibrant fibSp E
  have := Quillen.tensorLeft_isLeftQuillen K
  have := Quillen.isRightQuillen_of_isLeftQuillen (ihom.adjunction K)
  have hl (n : ℕ) : IsFibrant (level R n) := fibrant_levels K R n
  have hr (n : ℕ) : IsFibrant ((ihom K).obj (level R (n + 1))) := by
    have := hl (n + 1)
    exact Quillen.isFibrant_obj (ihom K) (level R (n + 1))
  have ht (n : ℕ) : weakEquivalences C (adjointStructureMap R n) ↔
      ∀ i, weakEquivalences SSet.{v}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((cosimplicialResolutionFamily cofC).obj.obj (G i))).map
          (adjointStructureMap R n)) := hdetect _
  rw [localObjects_localizingMaps_iff K cofC cofSp fibSp hcof G]
  exact ⟨fun h n ↦ (ht n).mpr (h n), fun h n ↦ (ht n).mp (h n)⟩

include hcof hdetect in
lemma localObjects_iff_omega (E : GeneralSymmetricSpectrum C K) [IsFibrant E] :
    Bousfield.localObjects cofSp fibSp (localizingMaps K G) E ↔ IsOmegaSpectrum E := by
  let R := (fibrantTarget fibSp).obj E
  let η : E ⟶ R := (fibrantTargetComparison fibSp).app E
  have : IsFibrant R := fibrantTarget_isFibrant fibSp E
  have : WeakEquivalence η := ⟨fibrantTargetComparison_weakEquivalence fibSp E⟩
  have hw (n : ℕ) : weakEquivalences C (levelMap η n) := by
    have := Quillen.isRightQuillen_of_isLeftQuillen (freeAtAdjunction (K := K) n)
    exact (weakEquivalence_iff _).mp
      (Quillen.map_weakEquivalence_of_fibrant (evaluation (K := K) n) η)
  exact (localObjects_iff_replacement_omega K cofC cofSp fibSp hcof G hdetect E).trans
    (isOmegaSpectrum_iff_of_levelWeakEquivalence η
      (fibrant_levels K E) (fibrant_levels K R) hw).symm

end SerrePositivity.SpectrumStabilization
