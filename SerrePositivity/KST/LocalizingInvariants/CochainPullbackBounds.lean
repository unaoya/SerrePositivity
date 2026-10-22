module

public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackLift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：元の複体 pullback は両脚の厳密な次数範囲を保持する。
方針：各次数の実 pullback の共同単射性により、両端が零なら頂点の恒等射も零。
規約：ホモロジーの下界とは区別する。使われ方：底を揃えた有限 Postnikov 模型。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.CochainPullback
variable {R : Type u} [CommRing R] {K L D : Complex R} (f : K ⟶ D) (g : L ⟶ D)

lemma component_isZero (i : ℤ) (hK : IsZero (K.X i)) (hL : IsZero (L.X i)) :
    IsZero ((pullback f g).X i) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply (graded f g i).hom_ext
  · exact hK.eq_of_tgt _ _
  · exact hL.eq_of_tgt _ _

lemma isStrictlyLE (n : ℤ) [K.IsStrictlyLE n] [L.IsStrictlyLE n] :
    (pullback f g).IsStrictlyLE n := by
  apply (CochainComplex.isStrictlyLE_iff _ n).2
  intro i hi
  exact component_isZero f g i (K.isZero_of_isStrictlyLE n i hi)
    (L.isZero_of_isStrictlyLE n i hi)

lemma isStrictlyGE (n : ℤ) [K.IsStrictlyGE n] [L.IsStrictlyGE n] :
    (pullback f g).IsStrictlyGE n := by
  apply (CochainComplex.isStrictlyGE_iff _ n).2
  intro i hi
  exact component_isZero f g i (K.isZero_of_isStrictlyGE n i hi)
    (L.isZero_of_isStrictlyGE n i hi)

end SerrePositivity.KST.LocalizingInvariants.CochainPullback
