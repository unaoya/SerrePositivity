module
public import SerrePositivity.PerfectComplex.TensorBaseChange

/-! # The signed cyclic action on tensor squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

attribute [reassoc] ιTensorObj_cochainTensorSymmetry

/-- Tensor maps act on homogeneous summands by ordinary tensor maps. -/
@[reassoc]
lemma ιTensorObj_cochainTensorMap {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P Q i j n h ≫ (cochainTensorMap f g).f n =
      (f.f i ⊗ₘ g.f j) ≫ ιTensorObj P' Q' i j n h := by
  rw [ι_mapBifunctorMap]
  change (f.f i ▷ Q.X j) ≫ (P'.X i ◁ g.f j) ≫ _ = _
  rw [tensorHom_def, Category.assoc]

/-- The signed symmetry is natural in both chain complexes. -/
@[reassoc]
lemma cochainTensorSymmetry_naturality {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    cochainTensorMap f g ≫ (cochainTensorSymmetry P' Q').hom =
      (cochainTensorSymmetry P Q).hom ≫ cochainTensorMap g f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ιTensorObj_cochainTensorMap_assoc, ιTensorObj_cochainTensorSymmetry,
    ιTensorObj_cochainTensorSymmetry_assoc]
  rw [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ιTensorObj_cochainTensorMap]
  simp only [BraidedCategory.braiding_naturality_assoc]

namespace Adams

/-- The standard total tensor square. -/
abbrev tensorSquare (P : CochainComplex (ModuleCat.{u} R) ℤ) := cochainTensor P P

/-- A chain map induces its tensor square. -/
abbrev tensorSquareMap {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    tensorSquare P ⟶ tensorSquare Q := cochainTensorMap f f

/-- The generator of the signed cyclic action of order two. -/
abbrev tensorSquareSwap (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquare P ⟶ tensorSquare P := (cochainTensorSymmetry P P).hom

@[simp]
lemma tensorSquareSwap_sq (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorSquareSwap P ≫ tensorSquareSwap P = 𝟙 _ := cochainTensorSymmetry_hom_comp P P

@[reassoc]
lemma tensorSquareSwap_naturality {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    tensorSquareMap f ≫ tensorSquareSwap Q = tensorSquareSwap P ≫ tensorSquareMap f :=
  cochainTensorSymmetry_naturality f f

lemma tensorSquare_perfect (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) : strictlyPerfectComplex R (tensorSquare P) :=
  strictlyPerfectComplex_cochainTensor P P hp hp

lemma tensorSquare_support {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hp : strictlyPerfectComplex R P)
    (hs : HasHomologySupportOn Z P) : HasHomologySupportOn Z (tensorSquare P) :=
  hs.cochainTensor_left hp P

/-- The homogeneous formula for the cyclic generator includes the Koszul sign. -/
lemma ιTensorObj_tensorSquareSwap (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j n : ℤ) (h : i + j = n) :
    ιTensorObj P P i j n h ≫ (tensorSquareSwap P).f n =
      (i * j).negOnePow • ((β_ (P.X i) (P.X j)).hom ≫
        ιTensorObj P P j i n (by omega)) :=
  ιTensorObj_cochainTensorSymmetry P P i j n h
end Adams
end SerrePositivity
