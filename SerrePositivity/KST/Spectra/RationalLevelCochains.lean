module

public import SerrePositivity.KST.Spectra.RationalHomotopyModules
public import SerrePositivity.KST.Spectra.TrivialHomotopyCohomology

/-!
概要：有理化スペクトルの各段の自明作用の高次 π_* の cochain の計算。
方針：telescope が与える有理係数構造を標数零の線形 cochain の計算へ入力する。
規約：係数構造の追加仮定は不要。これは Tot の π_* の計算の前段である。
使われ方：BF 1978 §2、Goerss–Jardine VIII §2。有理 Shapiro の cochain 消滅。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.RationalLevelCochains

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance rationalLiftCharZero : CharZero (ULift.{u} ℚ) where
  cast_injective _ _ h := Nat.cast_injective (R := ℚ) (congrArg ULift.down h)

local instance rationalCochainTrivialKan (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k : ℕ) :
    KanComplex (Action.trivial G ((OmegaSpectrum.rationalization X).level k).space).V.right :=
  inferInstanceAs (KanComplex ((OmegaSpectrum.rationalization X).level k).space.right)

/-- 概要：有理化の各段の高次 π_* の自明群 cochain の零次数は元の係数。
方針：実際の telescope の群の有理係数構造を供給して零次数の計算を適用する。
規約：任意の群を許し、係数体は群と宇宙を合わせた ULift ℚ を使う。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro における零行の同定。 -/
def zeroCohomologyIso (X : OmegaSpectrum.{u}) (k : ℕ) (G : Type u) [Group G] (q : ℕ) :
    (KanHomotopyGroup.cochainComplex (PointedActionCochains.obj
      (Action.trivial G ((OmegaSpectrum.rationalization X).level k).space)) q).homology 0 ≅
      AddCommGrpCat.of (TrivialHomotopyCochains.coefficient
        ((OmegaSpectrum.rationalization X).level k).space q) :=
  TrivialHomotopyCochains.zeroCohomologyIso
    ((OmegaSpectrum.rationalization X).level k).space (ULift.{u} ℚ) G q

/-- 概要：有限群の有理化各段の高次 π_* の自明 cochain は正次数で消滅する。
方針：telescope のテンソル積計算が与える加群構造を消滅定理へ渡す。
規約：q はホモトピー次数 q+2。Tot のホモトピー群の消滅とは主張しない。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の Tot の計算への入力。 -/
theorem positive_cohomology_isZero (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (q n : ℕ) :
    IsZero ((KanHomotopyGroup.cochainComplex (PointedActionCochains.obj
      (Action.trivial G ((OmegaSpectrum.rationalization X).level k).space)) q).homology
        (n + 1)) :=
  TrivialHomotopyCochains.positive_cohomology_isZero
    ((OmegaSpectrum.rationalization X).level k).space (ULift.{u} ℚ) G q n

end

end SerrePositivity.KST.Spectra.RationalLevelCochains
