module

public import SerrePositivity.CLMST.Almost
public import SerrePositivity.LengthAlgebra.Almost

/-! # mod p^N の perfectoid almost 同型と長さ

perfectoid ideal による零化から長さ零への条件を明示して受け取り、
その像イデアルに関する実 almost 同型から、元の環に制限して測る長さの一致を導く。
この一般入口では長さ零とmod p^Nの冪等性の証拠を引数で受ける。
具体的な完備塔への供給はNormalizedAlmostLengthで行う。
-/

@[expose] public section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory

variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (J : Ideal R)
    (lam : NormalizedLength R J)

/-- perfectoid ideal の零化が長さ零を与えるなら、mod p^N で almost 同型な対象の長さは一致。
元の perfectoid ideal の冪等性は仮定せず、mod p^N の像イデアルだけに要求する。 -/
theorem length_eq_of_perfectoid_mod_almost_iso (N : ℕ)
    [Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N)]
    (hzero : ∀ X : PowTorsionModule J,
      Almost.IsAlmostZero (perfectoidIdeal R p hR g) X.obj → lam.len X.obj = 0)
    {M M' : PowTorsionModule (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))}
    (e : (Almost.torsionLocalization (perfectoidIdealMod R p hR g N)
      (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))).obj M ≅
      (Almost.torsionLocalization (perfectoidIdealMod R p hR g N)
        (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))).obj M') :
    (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M.obj =
      (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M'.obj :=
  LengthAlgebra.length_eq_of_almost_iso_baseChange (perfectoidIdeal R p hR g) J lam
    Ideal.Quotient.mk_surjective hzero e

/-- mod p^N の全加群の almost 圏での同型から、元の正規化長さの一致を得る。
冪ねじれ部分圏への同型の移送を使い、原典の同型の範囲を保つ。 -/
theorem length_eq_of_perfectoid_mod_full_almost_iso (N : ℕ)
    [Fact (perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N)]
    (hzero : ∀ X : PowTorsionModule J,
      Almost.IsAlmostZero (perfectoidIdeal R p hR g) X.obj → lam.len X.obj = 0)
    {M M' : PowTorsionModule (J.map (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})))}
    (e : (Almost.localization (perfectoidIdealMod R p hR g N)).obj M.obj ≅
      (Almost.localization (perfectoidIdealMod R p hR g N)).obj M'.obj) :
    (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M.obj =
      (lam.comap (Ideal.Quotient.mk (Ideal.span {(p : R) ^ N})) _ le_rfl).len M'.obj :=
  LengthAlgebra.length_eq_of_full_almost_iso_baseChange (perfectoidIdeal R p hR g) J lam
    Ideal.Quotient.mk_surjective hzero e

end SerrePositivity.CLMST
