module

public import SerrePositivity.CommutativeAlgebra.Almost.SerreComparison
public import SerrePositivity.LengthAlgebra.SerreQuotient

/-! # almost 同型に対する長さの不変性

冪ねじれの almost zero 加群が長さ零という条件から、
actual な almost 局所化圏で同型となる対象の長さが一致することを証明する。
almost zero から長さ零への具体的な CLMST の結果は明示的な前提であり、
その文献結果そのものをこの一般的な接続と同一視しない。
-/

@[expose] public section
universe u
namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {R : Type u} [CommRing R] (I J : Ideal R) [Fact (I * I = I)]
    (lam : NormalizedLength R J)

/-- 冪ねじれの almost zero 対象の長さが零なら、almost 圏で同型な対象の長さは一致する。
局所化圏の射を分数で表す一般論と、長さの短完全列での加法性を使う。 -/
theorem length_eq_of_almost_iso
    (hzero : ∀ M : PowTorsionModule J, Almost.IsAlmostZero I M.obj → lam.len M.obj = 0)
    {M N : PowTorsionModule J}
    (e : (Almost.torsionLocalization I J).obj M ≅ (Almost.torsionLocalization I J).obj N) :
    lam.len M.obj = lam.len N.obj :=
  additiveLength_eq_of_localization_iso (Almost.torsionZeroObjects I J) (torsionLength lam)
    (torsionLength_iso lam) (torsionLength_add lam) hzero e

/-- 存在として述べた almost 同型からも長さの一致が従う。 -/
theorem length_eq_of_almost_isomorphic
    (hzero : ∀ M : PowTorsionModule J, Almost.IsAlmostZero I M.obj → lam.len M.obj = 0)
    {M N : PowTorsionModule J} (h : Almost.IsTorsionIsomorphic I J M N) :
    lam.len M.obj = lam.len N.obj := by
  obtain ⟨e⟩ := h
  exact length_eq_of_almost_iso I J lam hzero e

/-- 全加群の almost 圏での同型からも、冪ねじれ対象の長さの一致が従う。
冪ねじれ部分圏の局所化への同型の移送を証明して用いる。 -/
theorem length_eq_of_full_almost_iso
    (hzero : ∀ M : PowTorsionModule J, Almost.IsAlmostZero I M.obj → lam.len M.obj = 0)
    {M N : PowTorsionModule J}
    (e : (Almost.localization I).obj M.obj ≅ (Almost.localization I).obj N.obj) :
    lam.len M.obj = lam.len N.obj :=
  length_eq_of_almost_isomorphic I J lam hzero
    (Almost.isTorsionIsomorphic_of_iso I J M N e)

end SerrePositivity.LengthAlgebra
