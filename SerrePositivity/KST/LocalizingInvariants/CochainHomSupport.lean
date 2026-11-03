module

public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
概要：非正次数の源と下に有界な標的の内部 Hom が、同じ下界を持つことを示す。
方針：負次数の各斉次成分を、源または標的の零成分で消す。
規約：平坦性や有界上端の一様有限性を仮定しない。使われ方：有限 dg 切断への積の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants

lemma homComplex_lowerBound {R : Type u} [CommRing R] (P T : Complex R) (k : ℤ)
    [P.IsStrictlyLE 0] [T.IsStrictlyGE k] : (homComplex R P T).IsStrictlyGE k := by
  apply (CochainComplex.isStrictlyGE_iff _ k).2
  intro n hn
  change IsZero (ModuleCat.of R (Cochain P T n))
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun f g ↦ ?_⟩
  apply Cochain.ext
  intro i j hij
  by_cases hi : 0 < i
  · exact (P.isZero_of_isStrictlyLE 0 i hi).eq_of_src _ _
  · exact (T.isZero_of_isStrictlyGE k j (by omega)).eq_of_tgt _ _

lemma internalHom_lowerBound {R : Type u} [CommRing R] (P T : Complex R) (k : ℤ)
    [P.IsStrictlyLE 0] [T.IsStrictlyGE k] : ((ihom P).obj T).IsStrictlyGE k :=
  homComplex_lowerBound P T k

end SerrePositivity.KST.LocalizingInvariants
