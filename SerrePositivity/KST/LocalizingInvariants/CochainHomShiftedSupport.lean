module

public import SerrePositivity.KST.LocalizingInvariants.CochainHomSupport

/-!
概要：任意の次数の上下界から内部 Hom の差の下界を計算する。
方針：斉次写像の源か標的の零次数で各成分を消す。
規約：無限積や平坦性の仮定は不要。使われ方：集中した Postnikov 層への作用の降下。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R]

lemma homComplex_lowerBound_sub (P T : Complex R) (a b : ℤ)
    [P.IsStrictlyLE a] [T.IsStrictlyGE b] :
    (homComplex R P T).IsStrictlyGE (b - a) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).2
  intro n hn
  change IsZero (ModuleCat.of R (Cochain P T n))
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun f g ↦ ?_⟩
  apply Cochain.ext
  intro i j hij
  by_cases hi : a < i
  · exact (P.isZero_of_isStrictlyLE a i hi).eq_of_src _ _
  · exact (T.isZero_of_isStrictlyGE b j (by omega)).eq_of_tgt _ _

lemma homComplex_self_nonnegative (P : Complex R) (k : ℤ)
    [P.IsStrictlyLE k] [P.IsStrictlyGE k] : (homComplex R P P).IsStrictlyGE 0 := by
  simpa only [sub_self] using homComplex_lowerBound_sub P P k k

end SerrePositivity.KST.LocalizingInvariants
