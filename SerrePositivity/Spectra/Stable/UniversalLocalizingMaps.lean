module

public import SerrePositivity.Spectra.Stable.ModelCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameRightQuillen

/-! # Stabilization maps for every cofibrant coefficient are K-local equivalences

The chosen small generating family constructs the model. Its actual Omega
fibrancy criterion then proves the stabilization test for any cofibrant A,
including coefficients outside that family. No monoidal localization axiom
or ordinary suspension stability is assumed.
-/

@[expose] public section
universe w v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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
  (IP : MorphismProperty (GeneralSymmetricSpectrum C K))
  (p : StableModelPresentation.{w} K cofSp fibSp IP)
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include cofC hcof hfib in
lemma StableModelPresentation.localizingMap_isWeakEquivalence (n : ℕ) (A : C) [IsCofibrant A] :
    p.localization.model.categoryWithWeakEquivalences.weakEquivalences (localizingMap K n A) := by
  apply p.localization.weakEquivalences_eq.symm.le
  intro Y hY
  let RY := (fibrantTarget fibSp).obj Y
  have : IsFibrant RY := fibrantTarget_isFibrant fibSp Y
  have hRY : Bousfield.localObjects cofSp fibSp (localizingMaps K p.tests) RY :=
    (Bousfield.localObjects_iff_of_weakEquivalence cofSp fibSp hcof (localizingMaps K p.tests)
      ((fibrantTargetComparison fibSp).app Y)
      (fibrantTargetComparison_weakEquivalence fibSp Y)).mp hY
  have hΩ : IsFibrantOmegaSpectrum RY := (p.fibrant_iff RY).mp
    ((p.isLocalizationModel.fibrant_iff RY).mpr ⟨inferInstance, hRY⟩)
  apply (mappingTest_localizingMap_iff K cofC cofSp fibSp hcof n A Y).mpr
  let q := cosimplicialResolutionFamily cofC
  have := cosimplicialHom_isRightQuillen hcof hfib (q.obj.obj A) (q.cofibrant A)
    (q.atObject A).homotopicallyConstant
  have := Quillen.tensorLeft_isLeftQuillen K
  have := Quillen.isRightQuillen_of_isLeftQuillen (ihom.adjunction K)
  have := hΩ.1 n
  have := hΩ.1 (n + 1)
  have : IsFibrant ((ihom K).obj (level RY (n + 1))) :=
    Quillen.isFibrant_obj (ihom K) _
  have : WeakEquivalence (adjointStructureMap RY n) := ⟨hΩ.2 n⟩
  exact (weakEquivalence_iff _).mp
    (Quillen.map_weakEquivalence_of_fibrant (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (q.obj.obj A))
      (adjointStructureMap RY n))

end SerrePositivity.SpectrumStabilization
