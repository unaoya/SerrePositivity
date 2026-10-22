module

public import SerrePositivity.KST.LocalizingInvariants.CochainSeparatedBounds
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
概要：次数が上下界の隙間にある cochain の零性と、鎖ホモトピーの剛性を供給する。
方針：各成分で始域または終域の零性を使い、ホモトピーの境界式へ移す。
規約：実複体の厳密な上下界を使用。使われ方：零次数標的の経路の厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {P T : Complex R}

lemma cochainDegree_eq_zero_of_bounds (a b n : ℤ) [P.IsStrictlyLE a] [T.IsStrictlyGE b]
    (h : a + n < b) (c : Cochain P T n) : c = 0 := by
  apply Cochain.ext
  intro i j hij
  by_cases hi : a < i
  · exact (P.isZero_of_isStrictlyLE a i hi).eq_of_src _ _
  · exact (T.isZero_of_isStrictlyGE b j (by omega)).eq_of_tgt _ _

lemma cochainHom_eq_of_homotopy_bounds [P.IsStrictlyLE 0] [T.IsStrictlyGE 0]
    {f g : P ⟶ T} (h : Homotopy f g) : f = g := by
  let z := Cochain.equivHomotopy f g h
  have hz : z.val = 0 := cochainDegree_eq_zero_of_bounds 0 0 (-1) (by omega) z.val
  have he : Cochain.ofHom f = Cochain.ofHom g := by
    simpa only [hz, δ_zero, zero_add] using z.property
  apply HomologicalComplex.Hom.ext
  funext i
  simpa only [Cochain.ofHom_v] using Cochain.congr_v he i i (add_zero i)

end SerrePositivity.KST.LocalizingInvariants
