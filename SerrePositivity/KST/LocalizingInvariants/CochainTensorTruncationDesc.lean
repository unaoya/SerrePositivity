module

public import SerrePositivity.KST.LocalizingInvariants.CochainTruncationDesc
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
概要：非正次数の二つの複体から下に有界な標的への射を、両変数の smart 切断へ降ろす。
方針：内部 Hom の下界と左右の curry を使い、切断の普遍性を順に適用する。
規約：元の二変数射を厳密に回収。使われ方：非可換 dg 代数の有限 Postnikov 積。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.TruncationDesc

variable {R : Type u} [CommRing R]

lemma tensor_epi {A A' B B' : Complex R} (f : A ⟶ A') (g : B ⟶ B') [Epi f] [Epi g] :
    Epi (f ⊗ₘ g) := by
  have : (tensorRight B).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (tensorRightHomAdjunction B)
  have : (tensorLeft A').PreservesEpimorphisms := inferInstance
  rw [tensorHom_def]
  change Epi ((tensorRight B).map f ≫ (tensorLeft A').map g)
  infer_instance

def descendFirst {A B T : Complex R} (k : ℤ) [B.IsStrictlyLE 0] [T.IsStrictlyGE k]
    (f : A ⊗ B ⟶ T) : A.truncGE k ⊗ B ⟶ T := by
  have := homComplex_lowerBound B T k
  exact uncurryRight (descend k (curryRight f))

lemma projection_descendFirst {A B T : Complex R} (k : ℤ)
    [B.IsStrictlyLE 0] [T.IsStrictlyGE k] (f : A ⊗ B ⟶ T) :
    (A.πTruncGE k ⊗ₘ 𝟙 B) ≫ descendFirst k f = f := by
  have := homComplex_lowerBound B T k
  apply (tensorRightHomEquiv B A T).injective
  change curryRight ((A.πTruncGE k ⊗ₘ 𝟙 B) ≫
    uncurryRight (descend k (curryRight f))) = curryRight f
  rw [curryRight_naturality_source, curryRight_uncurryRight, projection_descend]

def descendSecond {A B T : Complex R} (k : ℤ) [A.IsStrictlyLE 0] [T.IsStrictlyGE k]
    (f : A ⊗ B ⟶ T) : A ⊗ B.truncGE k ⟶ T := by
  have := internalHom_lowerBound A T k
  exact uncurry (descend k (curry f))

lemma projection_descendSecond {A B T : Complex R} (k : ℤ)
    [A.IsStrictlyLE 0] [T.IsStrictlyGE k] (f : A ⊗ B ⟶ T) :
    (A ◁ B.πTruncGE k) ≫ descendSecond k f = f := by
  have := internalHom_lowerBound A T k
  change (A ◁ B.πTruncGE k) ≫ uncurry (descend k (curry f)) = f
  rw [← uncurry_natural_left, projection_descend, uncurry_curry]

def descendTensor {A B T : Complex R} (k : ℤ)
    [A.IsStrictlyLE 0] [B.IsStrictlyLE 0] [T.IsStrictlyGE k]
    (f : A ⊗ B ⟶ T) : A.truncGE k ⊗ B.truncGE k ⟶ T := by
  have := truncation_nonpositive A k
  exact descendSecond k (descendFirst k f)

lemma projection_descendTensor {A B T : Complex R} (k : ℤ)
    [A.IsStrictlyLE 0] [B.IsStrictlyLE 0] [T.IsStrictlyGE k] (f : A ⊗ B ⟶ T) :
    (A.πTruncGE k ⊗ₘ B.πTruncGE k) ≫ descendTensor k f = f := by
  have := truncation_nonpositive A k
  change (A.πTruncGE k ⊗ₘ B.πTruncGE k) ≫ descendSecond k (descendFirst k f) = f
  rw [tensorHom_def, Category.assoc, projection_descendSecond]
  simpa only [tensorHom_id] using projection_descendFirst k f

end SerrePositivity.KST.LocalizingInvariants.TruncationDesc
