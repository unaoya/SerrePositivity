module
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Homology.Factorizations.CM5a

/-! # Projective resolutions of bounded-above cochain complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace SerrePositivity
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Reverse degrees and take opposites back to the original abelian category. -/
def cochainUnop (K : CochainComplex Cᵒᵖ ℤ) : CochainComplex C ℤ :=
  ((CochainComplex.opEquivalence C).inverse.obj K).unop

def cochainUnopMap {K L : CochainComplex Cᵒᵖ ℤ} (f : K ⟶ L) :
    cochainUnop L ⟶ cochainUnop K :=
  ((CochainComplex.opEquivalence C).inverse.map f).unop

lemma cochainUnopMap_quasiIso {K L : CochainComplex Cᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] : QuasiIso (cochainUnopMap f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have hf : QuasiIsoAt f (-n) := inferInstance
  rw [quasiIsoAt_iff' _ (-(n + 1)) (-n) (-(n - 1)) (by simp; omega)
    (by simp; omega)] at hf
  have := hf
  exact ShortComplex.quasiIso_unopMap ((shortComplexFunctor' Cᵒᵖ (.up ℤ)
    (-(n + 1)) (-n) (-(n - 1))).map f)

/-- Every bounded-above complex has a bounded-above projective resolution,
with the same upper bound. -/
lemma exists_boundedAbove_projective_resolution [EnoughProjectives C]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyLE n] :
    ∃ (P : CochainComplex C ℤ) (ε : P ⟶ K) (_ : QuasiIso ε)
      (_ : ∀ i, Projective (P.X i)), P.IsStrictlyLE n := by
  let K' := (CochainComplex.opEquivalence C).functor.obj (op K)
  have : K'.IsStrictlyGE (-n) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE n (-i) (by omega)).op
  obtain ⟨L, i, hi, hL, hb⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K' (-n)
  let e : cochainUnop K' ≅ K :=
    ((CochainComplex.opEquivalence C).unitIso.app (op K)).unop
  have : QuasiIso (cochainUnopMap i) := cochainUnopMap_quasiIso i
  refine ⟨cochainUnop L, cochainUnopMap i ≫ e.hom, inferInstance, ?_, ?_⟩
  · intro q
    exact inferInstanceAs (Projective (unop (L.X (-q))))
  · rw [CochainComplex.isStrictlyLE_iff]
    intro q hq
    exact (L.isZero_of_isStrictlyGE (-n) (-q) (by omega)).unop

/-- A projective replacement that may extend arbitrarily far into negative degrees. -/
structure BoundedAboveProjectiveResolution (K : CochainComplex C ℤ) where
  complex : CochainComplex C ℤ
  bound : ℤ
  bounded : complex.IsStrictlyLE bound
  projective : ∀ i, Projective (complex.X i)
  π : complex ⟶ K
  quasiIso : QuasiIso π

namespace BoundedAboveProjectiveResolution
attribute [instance] bounded projective quasiIso
variable {K : CochainComplex C ℤ}

instance isKProjective (P : BoundedAboveProjectiveResolution K) : P.complex.IsKProjective :=
  CochainComplex.isKProjective_of_projective P.complex P.bound

/-- Choose a projective replacement without a finite projective dimension assumption. -/
def ofBoundedAbove [EnoughProjectives C] (K : CochainComplex C ℤ)
    (n : ℤ) [K.IsStrictlyLE n] : BoundedAboveProjectiveResolution K :=
  Classical.choice (by
    obtain ⟨P, ε, hε, hP, hb⟩ := exists_boundedAbove_projective_resolution K n
    exact ⟨⟨P, n, hb, hP, ε, hε⟩⟩)

/-- Comparison of any two replacements, compatible with their augmentations up to homotopy. -/
def comparison (P Q : BoundedAboveProjectiveResolution K) : P.complex ⟶ Q.complex :=
  (exists_lift_of_quasiIso Q.π P.π).choose

def comparisonHomotopy (P Q : BoundedAboveProjectiveResolution K) :
    Homotopy (comparison P Q ≫ Q.π) P.π :=
  (exists_lift_of_quasiIso Q.π P.π).choose_spec.some

lemma comparison_quasiIso (P Q : BoundedAboveProjectiveResolution K) :
    QuasiIso (comparison P Q) := by
  have : QuasiIso (comparison P Q ≫ Q.π) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap,
      (comparisonHomotopy P Q).homologyMap_eq i]
    infer_instance
  exact quasiIso_of_comp_right (comparison P Q) Q.π

/-- Different replacements are homotopy equivalent, with the chosen comparison as hom. -/
def comparisonHomotopyEquiv (P Q : BoundedAboveProjectiveResolution K) :
    HomotopyEquiv P.complex Q.complex :=
  ((CochainComplex.IsKProjective.quasiIso_iff (comparison P Q)).mp
    (comparison_quasiIso P Q)).choose

lemma comparisonHomotopyEquiv_hom (P Q : BoundedAboveProjectiveResolution K) :
    (comparisonHomotopyEquiv P Q).hom = comparison P Q :=
  ((CochainComplex.IsKProjective.quasiIso_iff (comparison P Q)).mp
    (comparison_quasiIso P Q)).choose_spec

end BoundedAboveProjectiveResolution

end SerrePositivity
