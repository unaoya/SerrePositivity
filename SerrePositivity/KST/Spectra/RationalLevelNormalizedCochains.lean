module

public import SerrePositivity.KST.Spectra.GroupNerveNormalizedCohomology
public import SerrePositivity.KST.Spectra.RationalHomotopyModules
public import SerrePositivity.KST.Spectra.TrivialHomotopyAction

/-!
概要：有理化スペクトルの各段の高次群を係数とする BG の正規化 cochain の消滅。
方針：telescope から得た有理作用を、正規化群 cochain の標数零の計算へ入力する。
規約：実際の有理化対象の群を使う。写像空間の π_* はまだ計算しない。
使われ方：BF 1978 §2、Goerss–Jardine VIII §2。有理 Shapiro の正規化 cochain の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.RationalLevelNormalizedCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance normalizedLiftCharZero : CharZero (ULift.{u} ℚ) where
  cast_injective _ _ h := Nat.cast_injective (R := ℚ) (congrArg ULift.down h)

/-- 概要：有理化各段の高次群係数の BG の正規化 cochain の零次数は元の係数。
方針：実際の有理係数作用を供給して自明作用の零次数の比較を使う。
規約：q はホモトピー次数 q+2。群の有限性は不要。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の正規化 cochain の零行。 -/
def zeroCohomologyIso (X : OmegaSpectrum.{u}) (k : ℕ) (G : Type u) [Group G] (q : ℕ) :
    (NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of (TrivialHomotopyCochains.coefficient
        ((OmegaSpectrum.rationalization X).level k).space q))).homology 0 ≅
      AddCommGrpCat.of (TrivialHomotopyCochains.coefficient
        ((OmegaSpectrum.rationalization X).level k).space q) :=
  GroupNerve.normalizedZeroCohomologyIso G (ULift.{u} ℚ)
    (TrivialHomotopyCochains.coefficient ((OmegaSpectrum.rationalization X).level k).space q)

/-- 概要：有限群の有理化各段の高次群係数の正規化 cochain は正次数で消滅。
方針：実際の telescope の群の有理作用を標数零の正規化群 cochain の結果へ渡す。
規約：この結果だけで塔の収束や Tot の群を主張しない。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の幾何的微分と比較する入力。 -/
theorem positive_cohomology_isZero (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (q n : ℕ) :
    IsZero ((NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of (TrivialHomotopyCochains.coefficient
        ((OmegaSpectrum.rationalization X).level k).space q))).homology (n + 1)) :=
  GroupNerve.normalized_positive_cohomology_isZero G (ULift.{u} ℚ)
    (TrivialHomotopyCochains.coefficient ((OmegaSpectrum.rationalization X).level k).space q) n

end

end SerrePositivity.KST.Spectra.RationalLevelNormalizedCochains
