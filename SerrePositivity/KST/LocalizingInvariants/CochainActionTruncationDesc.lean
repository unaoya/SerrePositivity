module

public import SerrePositivity.KST.LocalizingInvariants.CochainHomShiftedSupport
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc

/-!
概要：集中次数 k を持つ複体への左右の作用射を、代数変数の τ≥a へ降ろす。
方針：自己内部 Hom の下界零と curry の自然性を使う。
規約：元の作用射を厳密に回収する。使われ方：Postnikov 層の底への作用の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.ActionDesc
variable {R : Type u} [CommRing R] {A P : Complex R} (k a : ℤ)
  [P.IsStrictlyLE k] [P.IsStrictlyGE k]

def left (ha : a ≤ 0) (f : A ⊗ P ⟶ P) : A.truncGE a ⊗ P ⟶ P := by
  have : (homComplex R P P).IsStrictlyGE 0 := homComplex_self_nonnegative P k
  have : (homComplex R P P).IsStrictlyGE a :=
    (homComplex R P P).isStrictlyGE_of_ge a 0 ha
  exact uncurryRight (TruncationDesc.descend a (curryRight f))

lemma projection_left (ha : a ≤ 0) (f : A ⊗ P ⟶ P) :
    (A.πTruncGE a ▷ P) ≫ left k a ha f = f := by
  have : (homComplex R P P).IsStrictlyGE 0 := homComplex_self_nonnegative P k
  have : (homComplex R P P).IsStrictlyGE a :=
    (homComplex R P P).isStrictlyGE_of_ge a 0 ha
  apply (tensorRightHomEquiv P A P).injective
  change curryRight ((A.πTruncGE a ▷ P) ≫
    uncurryRight (TruncationDesc.descend a (curryRight f))) = curryRight f
  rw [← tensorHom_id, curryRight_naturality_source, curryRight_uncurryRight,
    TruncationDesc.projection_descend]

def right (ha : a ≤ 0) (f : P ⊗ A ⟶ P) : P ⊗ A.truncGE a ⟶ P := by
  have : ((ihom P).obj P).IsStrictlyGE 0 := homComplex_self_nonnegative P k
  have : ((ihom P).obj P).IsStrictlyGE a :=
    ((ihom P).obj P).isStrictlyGE_of_ge a 0 ha
  exact uncurry (TruncationDesc.descend a (curry f))

lemma projection_right (ha : a ≤ 0) (f : P ⊗ A ⟶ P) :
    (P ◁ A.πTruncGE a) ≫ right k a ha f = f := by
  have : ((ihom P).obj P).IsStrictlyGE 0 := homComplex_self_nonnegative P k
  have : ((ihom P).obj P).IsStrictlyGE a :=
    ((ihom P).obj P).isStrictlyGE_of_ge a 0 ha
  change (P ◁ A.πTruncGE a) ≫ uncurry (TruncationDesc.descend a (curry f)) = f
  rw [← uncurry_natural_left, TruncationDesc.projection_descend, uncurry_curry]

end SerrePositivity.KST.LocalizingInvariants.ActionDesc
