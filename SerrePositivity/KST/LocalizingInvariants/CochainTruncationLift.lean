module

public import SerrePositivity.KST.LocalizingInvariants.CochainConnectiveLift

/-!
概要：任意の上界 k を持つ複体からの射を、smart τ≤k へ一意に持ち上げる。
方針：源の切断包含の実逆と、切断の自然性を使う。
規約：元の chain map を厳密に回収。使われ方：Postnikov 層への左右作用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.TruncationLift
variable {R : Type u} [CommRing R] {P T : Complex R}

def lift (k : ℤ) [P.IsStrictlyLE k] (f : P ⟶ T) : P ⟶ T.truncLE k :=
  inv (P.ιTruncLE k) ≫ CochainComplex.truncLEMap f k

lemma lift_inclusion (k : ℤ) [P.IsStrictlyLE k] (f : P ⟶ T) :
    lift k f ≫ T.ιTruncLE k = f := by
  rw [lift, Category.assoc, CochainComplex.ιTruncLE_naturality, IsIso.inv_hom_id_assoc]

lemma lift_unique (k : ℤ) [P.IsStrictlyLE k] (f : P ⟶ T) (g : P ⟶ T.truncLE k)
    (hg : g ≫ T.ιTruncLE k = f) : g = lift k f := by
  have : Mono (T.ιTruncLE k) := by
    change Mono (HomologicalComplex.ιTruncLE T (ComplexShape.embeddingUpIntLE k))
    infer_instance
  apply (cancel_mono (T.ιTruncLE k)).1
  rw [hg, lift_inclusion]

end SerrePositivity.KST.LocalizingInvariants.TruncationLift
