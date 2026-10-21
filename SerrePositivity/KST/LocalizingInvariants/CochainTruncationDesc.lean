module

public import SerrePositivity.KST.LocalizingInvariants.CochainHomSupport

/-!
概要：下界を持つ複体への元の射を、smart 切断 τ≥k から一意に降下する。
方針：標的の切断射影が実同型になることを使い、自然性から元の射を回収する。
規約：実射の等号を保持。使われ方：dg 積の二変数への切断の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.TruncationDesc

variable {R : Type u} [CommRing R]

instance projection_epi (A : Complex R) (k : ℤ) : Epi (A.πTruncGE k) := by
  change Epi (HomologicalComplex.πTruncGE A (embeddingUpIntGE k))
  infer_instance

instance projection_component_epi (A : Complex R) (k i : ℤ) : Epi ((A.πTruncGE k).f i) := by
  change Epi ((HomologicalComplex.πTruncGE A (embeddingUpIntGE k)).f i)
  infer_instance

def descend {A T : Complex R} (k : ℤ) [T.IsStrictlyGE k] (f : A ⟶ T) : A.truncGE k ⟶ T :=
  CochainComplex.truncGEMap f k ≫ inv (T.πTruncGE k)

lemma projection_descend {A T : Complex R} (k : ℤ) [T.IsStrictlyGE k] (f : A ⟶ T) :
    A.πTruncGE k ≫ descend k f = f := by
  rw [descend, ← Category.assoc, CochainComplex.πTruncGE_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

lemma descend_unique {A T : Complex R} (k : ℤ) [T.IsStrictlyGE k] (f : A ⟶ T)
    (g : A.truncGE k ⟶ T) (hg : A.πTruncGE k ≫ g = f) : g = descend k f := by
  apply (cancel_epi (A.πTruncGE k)).1
  rw [hg, projection_descend]

lemma truncation_nonpositive (A : Complex R) (k : ℤ) [A.IsStrictlyLE 0] :
    (A.truncGE k).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ 0).2
  intro i hi
  exact IsZero.of_epi ((A.πTruncGE k).f i) (A.isZero_of_isStrictlyLE 0 i hi)

end SerrePositivity.KST.LocalizingInvariants.TruncationDesc
