module

public import SerrePositivity.Spectra.General.CotensorStructure
public import SerrePositivity.Spectra.General.ParametrizedCotensor
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroModuleMap

/-! # Cotensor bifunctor on the levels of general symmetric spectra -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.GeneralSymmetricSpectrum

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C] {K : C}

/-- At each level the cotensor bifunctor acts by precomposition and postcomposition. -/
lemma cotensorBimap_app (q : ℕ) {X Y : C} (f : X ⟶ Y)
    {E F : GeneralSymmetricSpectrum C K} (g : E ⟶ F) :
    (((cotensorBifunctor.map f.op).app E ≫ (cotensorFunctor X).map g).hom).app
        (FiniteBijection.of q) =
      (pre f).app (level E q) ≫ (ihom X).map (g.hom.app (FiniteBijection.of q)) := by
  let bimap := (cotensorBifunctor.map f.op).app E ≫ (cotensorFunctor X).map g
  have h := SymmetricSequence.freeZeroModuleMap_law (SymmetricSequence.tensorPowerSequence K) f g
    (internalHomCotensorIso Y E) (internalHomCotensorIso X F) bimap
    (homBySequenceCotensorIso Y E) (homBySequenceCotensorIso X F) (Iso.refl _) (Iso.refl _)
    (by
      simp only [Iso.refl_hom, Category.id_comp]
      rfl)
    (by
      change _ =
        (MonoidalModuleInternalHom.freeHomIso (SymmetricSequence.tensorPowerSequence K)
          ((SymmetricSequence.freeAt 0).obj X) F).hom ≫
          (homBySequenceCotensorIso X F).hom ≫ 𝟙 (SymmetricSequence.unshiftedInternalHom X F.X)
      rw [Category.comp_id]
      rfl)
    (by
      change (internalHomCotensorIso Y E).inv ≫
        (MonoidalModuleInternalHom.preMap _ ((freeAt 0).map f) E ≫
          (internalHomFunctor ((freeAt 0).obj X)).map g) ≫
          (internalHomCotensorIso X F).hom = bimap
      simp only [Category.assoc]
      exact FunctorTransport.bimap_conjugate internalHomCotensorBifunctorIso f.op g)
    rfl rfl
  have hq := SymmetricSequence.unshiftedInternalHomMapLaw_app f g.hom _ q h
  simp only [Iso.refl_inv, Iso.refl_hom, Category.comp_id] at hq
  change (𝟙 (cotensor Y E).X ≫ bimap.hom).app (FiniteBijection.of q) = _ at hq
  rw [Category.id_comp] at hq
  exact hq

end SerrePositivity.GeneralSymmetricSpectrum
