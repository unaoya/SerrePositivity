module
public import SerrePositivity.DifferentialGraded.Tensor.KFlat
public import SerrePositivity.HomologicalAlgebra.CochainTensorAcyclic

/-! # A上のK-flat複体の単位・shift・cone・tensor閉性 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A]

lemma complexKFlat_unit : complexKFlat A (𝟙_ (Complex A)) := by
  intro L hL
  exact cochainAcyclic_of_iso hL (λ_ L).symm

lemma complexKFlat_shift {K : Complex A} (h : complexKFlat A K) (s : ℤ) :
    complexKFlat A (K⟦s⟧) := by
  intro L hL
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (h L hL) s)
    (cochainTensorShiftLeft K L s).symm

lemma complexKFlat_cone {K K' : Complex A} (f : K ⟶ K')
    (hK : complexKFlat A K) (hK' : complexKFlat A K') :
    complexKFlat A (mappingCone f) := by
  intro L hL
  exact cochainAcyclic_of_iso
    (cochainAcyclic_mappingCone (cochainTensorMap f (𝟙 L)) (hK L hL) (hK' L hL))
    (cochainTensorConeLeft f L).symm

lemma complexKFlat_tensor {K K' : Complex A} (hK : complexKFlat A K)
    (hK' : complexKFlat A K') : complexKFlat A (K ⊗ K') := by
  intro L hL
  exact cochainAcyclic_of_iso (hK (K' ⊗ L) (hK' L hL)) (α_ K K' L).symm

/-- 両側に有界なflat複体とのtensorは、相手が非有界でもacyclic性を保つ。 -/
lemma complexKFlat_of_flat_bounds (K : Complex A) (a b : ℤ)
    (ha : ∀ i, i < a → IsZero (K.X i)) (hb : ∀ i, b < i → IsZero (K.X i))
    (hflat : ∀ i, Module.Flat A (K.X i)) : complexKFlat A K := by
  intro L hL
  exact cochainTensor_acyclic_of_flat_bounds K L a b ha hb hflat hL

/-- K-flatな右因子とのtensorは任意の準同型を保つ。 -/
lemma complexKFlat_quasiIso_left {K : Complex A} (hK : complexKFlat A K)
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap f (𝟙 K)) := by
  have hc := (cochain_quasiIso_iff_cone_acyclic f).1 inferInstance
  have ht := cochainAcyclic_of_iso (hK (mappingCone f) hc)
    (cochainTensorSymmetry K (mappingCone f))
  exact (cochain_quasiIso_iff_cone_acyclic _).2
    (cochainAcyclic_of_iso ht (cochainTensorConeLeft f K))

/-- K-flatな左因子とのtensorは任意の準同型を保つ。 -/
lemma complexKFlat_quasiIso_right {K : Complex A} (hK : complexKFlat A K)
    {L L' : Complex A} (f : L ⟶ L') [QuasiIso f] :
    QuasiIso (cochainTensorMap (𝟙 K) f) := by
  have := complexKFlat_quasiIso_left A hK f
  have : QuasiIso (cochainTensorMap (𝟙 K) f ≫ (cochainTensorSymmetry K L').hom) := by
    rw [cochainTensorSymmetry_naturality]
    infer_instance
  exact quasiIso_of_comp_right _ (cochainTensorSymmetry K L').hom

/-- 非有界acyclicの消滅条件と、任意の準同型の保存は同値。 -/
lemma complexKFlat_iff_preserves_quasiIso (K : Complex A) :
    complexKFlat A K ↔ ∀ {L L' : Complex A} (f : L ⟶ L'),
      QuasiIso f → QuasiIso (cochainTensorMap (𝟙 K) f) := by
  constructor
  · intro h L L' f hf
    have := hf
    exact complexKFlat_quasiIso_right A h f
  · intro h L hL
    have h₀ : (0 : Complex A).Acyclic := acyclic_of_isZero _ (isZero_zero _)
    have hf : QuasiIso (0 : L ⟶ (0 : Complex A)) := ⟨fun n =>
      (quasiIsoAt_iff_exactAt' _ n (h₀ n)).2 (hL n)⟩
    have := h (0 : L ⟶ (0 : Complex A)) hf
    have hz : (K ⊗ (0 : Complex A)).Acyclic :=
      acyclic_of_isZero _ ((tensorLeft K).map_isZero (isZero_zero _))
    intro n
    exact (exactAt_iff_of_quasiIsoAt (cochainTensorMap (𝟙 K) (0 : L ⟶ (0 : Complex A))) n).2
      (hz n)

end SerrePositivity.DifferentialGraded
