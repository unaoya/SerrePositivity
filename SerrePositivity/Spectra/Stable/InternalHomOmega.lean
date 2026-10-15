module

public import SerrePositivity.Spectra.General.ShiftedHomAdjoint
public import SerrePositivity.Spectra.General.Cotensor
public import SerrePositivity.Spectra.Stable.Omega
public import SerrePositivity.HomotopicalAlgebra.Quillen.FibrantCriterion
public import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-! # Internal Hom from free cofibrant coefficients preserves Omega spectra

The actual bonding-map formula factors into a mapped original bonding map
and two isomorphisms. Brown preservation for ihom proves the weak-equivalence
condition. Cotensor follows through the actual free-zero module comparison.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.GeneralSymmetricSpectrum

namespace SerrePositivity.SpectrumStabilization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [ModelCategory C] {K : C}

omit [HasLimitsOfSize.{0, 0} C] in
lemma isOmegaSpectrum_iff_of_iso {E F : GeneralSymmetricSpectrum C K} (e : E ≅ F) :
    IsOmegaSpectrum E ↔ IsOmegaSpectrum F := by
  have he (n : ℕ) : weakEquivalences C (adjointStructureMap E n) ↔
      weakEquivalences C (adjointStructureMap F n) :=
    (weakEquivalences C).arrow_mk_iso_iff
      (Arrow.isoMk ((evaluation (K := K) n).mapIso e)
        ((ihom K).mapIso ((evaluation (K := K) (n + 1)).mapIso e))
        (adjointStructureMap_naturality e.hom n))
  exact ⟨fun h n ↦ (he n).mp (h n), fun h n ↦ (he n).mpr (h n)⟩

omit [HasLimitsOfSize.{0, 0} C] in
lemma isFibrantOmegaSpectrum_iff_of_iso {E F : GeneralSymmetricSpectrum C K} (e : E ≅ F) :
    IsFibrantOmegaSpectrum E ↔ IsFibrantOmegaSpectrum F := by
  have hf {A B : GeneralSymmetricSpectrum C K} (a : A ≅ B)
      (hB : ∀ n, IsFibrant (level B n)) (n : ℕ) : IsFibrant (level A n) := by
    have : IsFibrant ((evaluation (K := K) n).obj B) := hB n
    let eN : level A n ≅ level B n := (evaluation (K := K) n).mapIso a
    have : Fibration eN.hom := ⟨(fibrations C).of_isIso eN.hom⟩
    exact isFibrant_of_fibration eN.hom
  exact ⟨fun h ↦ ⟨hf e.symm h.1, (isOmegaSpectrum_iff_of_iso e).mp h.2⟩,
    fun h ↦ ⟨hf e h.1, (isOmegaSpectrum_iff_of_iso e).mpr h.2⟩⟩

variable [Quillen.IsQuillenBifunctor (curriedTensor C)] [IsCofibrant K]

lemma shiftedHom_isFibrantOmega (n : ℕ) (X : C) [IsCofibrant X]
    (E : GeneralSymmetricSpectrum C K) (hE : IsFibrantOmegaSpectrum E) :
    IsFibrantOmegaSpectrum (shiftedHom n X E) := by
  have := Quillen.tensorLeft_isLeftQuillen X
  have := Quillen.isRightQuillen_of_isLeftQuillen (ihom.adjunction X)
  have := Quillen.tensorLeft_isLeftQuillen K
  have := Quillen.isRightQuillen_of_isLeftQuillen (ihom.adjunction K)
  constructor
  · intro q
    have := hE.1 (n + q)
    exact Quillen.isFibrant_obj (ihom X) (level E (n + q))
  · intro q
    have := hE.1 (n + q)
    have := hE.1 ((n + q) + 1)
    have : IsFibrant ((ihom K).obj (level E ((n + q) + 1))) :=
      Quillen.isFibrant_obj (ihom K) _
    have : WeakEquivalence (adjointStructureMap E (n + q)) := ⟨hE.2 (n + q)⟩
    have hw : weakEquivalences C ((ihom X).map (adjointStructureMap E (n + q))) :=
      (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_fibrant (ihom X) _)
    have hi : IsIso (shiftedHomSuspensionIndex n q) := inferInstance
    have : IsIso (E.X.map (shiftedHomSuspensionIndex n q)) :=
      inferInstanceAs (IsIso
        ((SymmetricSequence.toFunctorCategory.obj E.X).map (shiftedHomSuspensionIndex n q)))
    let outputIso := (SymmetricSequence.toFunctorCategory.obj E.X).mapIso
      (asIso (shiftedHomSuspensionIndex n q))
    let eTail := (ihom K).mapIso ((ihom X).mapIso outputIso)
    have ht : weakEquivalences C
        ((ihom K).map ((ihom X).map (E.X.map (shiftedHomSuspensionIndex n q)))) :=
      (weakEquivalences C).of_isIso eTail.hom
    rw [shiftedHom_adjointStructureMap_formula]
    exact (weakEquivalences C).comp_mem _ _
      ((weakEquivalences C).comp_mem _ _ hw ((weakEquivalences C).of_isIso _))
      ht

lemma internalHomFreeAt_isFibrantOmega (n : ℕ) (X : C) [IsCofibrant X]
    (E : GeneralSymmetricSpectrum C K) (hE : IsFibrantOmegaSpectrum E) :
    IsFibrantOmegaSpectrum (internalHom ((freeAt (K := K) n).obj X) E) :=
  (isFibrantOmegaSpectrum_iff_of_iso (internalHomShiftIso n X E)).mpr
    (shiftedHom_isFibrantOmega n X E hE)

lemma cotensor_isFibrantOmega (X : C) [IsCofibrant X]
    (E : GeneralSymmetricSpectrum C K) (hE : IsFibrantOmegaSpectrum E) :
    IsFibrantOmegaSpectrum (cotensor X E) :=
  (isFibrantOmegaSpectrum_iff_of_iso (internalHomCotensorIso X E)).mp
    (internalHomFreeAt_isFibrantOmega 0 X E hE)

end SerrePositivity.SpectrumStabilization
