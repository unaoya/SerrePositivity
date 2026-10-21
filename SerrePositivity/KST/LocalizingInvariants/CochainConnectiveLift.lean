module

public import SerrePositivity.DifferentialGraded.Complexes.Monoidal
public import SerrePositivity.HomologicalAlgebra.CochainTensorBounds
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：非正次数の複体からの元の射を、smart connective cover へ一意に持ち上げる。
方針：源の τ≤0 の包含が実同型となることを使い、切断の自然性から元の射を回収する。
規約：ホモロジー同型だけで射を選ばない。使われ方：dg 代数の実単位・積の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.ConnectiveLift

variable {R : Type u} [CommRing R] {A B : Complex R} [A.IsStrictlyLE 0]

def lift (f : A ⟶ B) : A ⟶ B.truncLE 0 :=
  inv (A.ιTruncLE 0) ≫ CochainComplex.truncLEMap f 0

lemma lift_inclusion (f : A ⟶ B) : lift f ≫ B.ιTruncLE 0 = f := by
  rw [lift, Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

lemma lift_unique (f : A ⟶ B) (g : A ⟶ B.truncLE 0) (hg : g ≫ B.ιTruncLE 0 = f) :
    g = lift f := by
  haveI : Mono (B.ιTruncLE 0) := by
    change Mono (HomologicalComplex.ιTruncLE B (ComplexShape.embeddingUpIntLE 0))
    infer_instance
  apply (cancel_mono (B.ιTruncLE 0)).1
  rw [hg, lift_inclusion]

instance unit_nonpositive : (𝟙_ (Complex R)).IsStrictlyLE 0 := by
  apply (CochainComplex.isStrictlyLE_iff _ 0).2
  intro i hi
  change IsZero (cochainTensorUnit.X i)
  have he : (0 : ℤ) ≠ i := by omega
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
    (ModuleCat.of R R) i he.symm

lemma tensor_nonpositive (P Q : Complex R) [P.IsStrictlyLE 0] [Q.IsStrictlyLE 0] :
    (P ⊗ Q).IsStrictlyLE 0 := by
  change (cochainTensor P Q).IsStrictlyLE 0
  simpa only [add_zero] using cochainTensor_isStrictlyLE P Q 0 0

end SerrePositivity.KST.LocalizingInvariants.ConnectiveLift
