module

public import SerrePositivity.KST.Spectra.GroupNerveCochainComparison
public import SerrePositivity.KST.Spectra.TrivialHomotopyCochainComplex
public import SerrePositivity.KST.Spectra.RationalCochainCohomology
public import SerrePositivity.KST.Spectra.ZeroCochainCohomology

/-!
概要：BG の正規化 cochain の零次数の計算と有限群の標数零係数の正次数の消滅。
方針：全単体の cochain の正規化ホモトピー同値と非斉次群 cochain の比較を合成する。
規約：cochain の cohomology の計算であり、写像空間や Tot の π_* とはまだ同定しない。
使われ方：Goerss–Jardine III §2、VIII §2。有理 Shapiro の正規化 cochain の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.GroupNerve

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (G R : Type u) [Group G] [CommRing R]
  (M : Type u) [AddCommGroup M] [Module R M]

/-- 概要：BG の正規化 cochain の cohomology は自明係数の群 cochain の cohomology。
方針：正規化の同値、群座標の複体同型、加群忘却の homology 比較を合成する。
規約：任意の複体次数。係数は R 加群。
使われ方：Goerss–Jardine VIII §2。有限群の群 cohomology の計算の移送。 -/
def normalizedCohomologyIso (n : ℕ) :
    (NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of M)).homology n ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((LinearGroupCochains.complex (Rep.trivial R G M)).homology n) :=
  ((SimplicialValueCochains.normalizationHomotopyEquiv
    (nerve (AsSmall.{u} (SingleObj G))) (AddCommGrpCat.of M)).toHomologyIso n).symm ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n).mapIso
      (linearComplexIso G R M) ≪≫
    TrivialHomotopyCochains.forgetHomologyIso R
      (LinearGroupCochains.complex (Rep.trivial R G M)) n

/-- 概要：BG の正規化 cochain の零次数 cohomology は元の係数。
方針：自明作用の群 cochain の零次数の同型を忘却して合成する。
規約：群の有限性と標数零は不要。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の零行の比較先。 -/
def normalizedZeroCohomologyIso :
    (NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of M)).homology 0 ≅ AddCommGrpCat.of M :=
  normalizedCohomologyIso G R M 0 ≪≫
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapIso
      (LinearGroupCochains.zeroCohomologyIsoOfTrivial (Rep.trivial R G M))

end

section

/-- 概要：有限群の BG の標数零係数の正規化 cochain は正次数で消滅する。
方針：非斉次群 cochain の消滅を忘却し、正規化の比較同型で戻す。
規約：写像空間の π_* の消滅はこの cochain の結果だけから主張しない。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の幾何的な塔と比較する代数的消滅。 -/
theorem normalized_positive_cohomology_isZero (G R : Type u) [Group G] [Finite G]
    [Field R] [CharZero R] (M : Type u) [AddCommGroup M] [Module R M] (n : ℕ) :
    IsZero ((NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of M)).homology (n + 1)) := by
  have h := LinearGroupCochains.positive_cohomology_isZero (Rep.trivial R G M) n
  have hf := (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map_isZero h
  exact hf.of_iso (normalizedCohomologyIso G R M (n + 1))

end

end SerrePositivity.KST.Spectra.GroupNerve
