module

public import SerrePositivity.Spectra.Stable.CofibrantLocalizingMaps
public import SerrePositivity.Spectra.Stable.LocalizingHom
public import SerrePositivity.HomotopicalAlgebra.Localization.FrameArrowTests
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

/-! # Computing the ordinary stabilization locality test by bonding maps

The source frames are actual free images of a cofibrant resolution in C.
Their augmentations are weak by Brown's lemma on cofibrant objects. The
shared frame-arrow comparison identifies the original spectral RMap test,
and the actual adjunction arrow isomorphism identifies its bonding map.
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

include hcof in
lemma mappingTest_localizingMap_iff (n : ℕ) (X : C) [IsCofibrant X]
    (E : GeneralSymmetricSpectrum C K) :
    Bousfield.mappingTest cofSp fibSp E (localizingMap K n X) ↔
      weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        ((cosimplicialResolutionFamily cofC).obj.obj X)).map
          (adjointStructureMap ((fibrantTarget fibSp).obj E) n)) := by
  let q := cosimplicialResolutionFamily cofC
  let A := q.obj.obj X
  let a := q.augmentation.app X
  let L := tensorRight K ⋙ freeAt (K := K) (n + 1)
  let F := freeAt (K := K) n
  let t := Functor.whiskerLeft A (stabilizationMap K n)
  let aL := Functor.whiskerRight a L ≫ (Functor.constComp SimplexCategory X L).hom
  let aF := Functor.whiskerRight a F ≫ (Functor.constComp SimplexCategory X F).hom
  have := Quillen.tensorRight_isLeftQuillen K
  have : L.IsLeftAdjoint := (bondingAdjunction K n).isLeftAdjoint
  have : F.IsLeftAdjoint := (freeAtAdjunction (K := K) n).isLeftAdjoint
  have : Quillen.IsLeftQuillen L := inferInstance
  have ha (m : SimplexCategory) : weakEquivalences C (a.app m) :=
    (q.atObject X).augmentation_weakEquivalence m
  have hs : t ≫ aF = aL ≫
      (Functor.const SimplexCategory).map (localizingMap K n X) := by
    apply NatTrans.ext
    funext m
    change localizingMap K n (A.obj m) ≫ (F.map (a.app m) ≫ 𝟙 _) =
      (L.map (a.app m) ≫ 𝟙 _) ≫ localizingMap K n X
    simp only [Category.comp_id]
    exact (localizingMap_naturality K n (a.app m)).symm
  have haL (m : SimplexCategory) : weakEquivalences _ (aL.app m) := by
    simpa only [aL, NatTrans.comp_app, Functor.constComp, Category.comp_id] using
      leftQuillen_frame_augmentation_weakEquivalence L A (q.cofibrant X) a ha m
  have haF (m : SimplexCategory) : weakEquivalences _ (aF.app m) := by
    simpa only [aF, NatTrans.comp_app, Functor.constComp, Category.comp_id] using
      leftQuillen_frame_augmentation_weakEquivalence F A (q.cofibrant X) a ha m
  have he := Bousfield.FrameArrowTests.mappingTest_iff cofSp fibSp hcof
    (localizingMap K n X) t aL aF hs
    (leftQuillen_frame_reedyCofibrant L A (q.cofibrant X))
    (leftQuillen_frame_reedyCofibrant F A (q.cofibrant X))
    haL haF E
  exact he.trans ((weakEquivalences SSet.{v}).arrow_mk_iso_iff
    (localizingHomArrowIso K n A ((fibrantTarget fibSp).obj E)))

include hcof in
lemma localObjects_localizingMaps_iff {ι : Type t} (G : ι → C)
    [∀ i, IsCofibrant (G i)] (E : GeneralSymmetricSpectrum C K) :
    Bousfield.localObjects cofSp fibSp (localizingMaps K G) E ↔
      ∀ (n : ℕ) (i : ι), weakEquivalences SSet.{v} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom
        ((cosimplicialResolutionFamily cofC).obj.obj (G i))).map
          (adjointStructureMap ((fibrantTarget fibSp).obj E) n)) := by
  constructor
  · intro h n i
    exact (mappingTest_localizingMap_iff K cofC cofSp fibSp hcof n (G i) E).mp
      (h _ (MorphismProperty.ofHoms.mk (n, i)))
  · intro h X Y f hf
    cases hf with
    | mk p => exact
        (mappingTest_localizingMap_iff K cofC cofSp fibSp hcof p.1 (G p.2) E).mpr (h p.1 p.2)

end SerrePositivity.SpectrumStabilization
