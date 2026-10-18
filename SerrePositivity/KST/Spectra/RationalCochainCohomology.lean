module

public import SerrePositivity.KST.Spectra.RepresentationCochainComparison

/-!
概要：有限群の標数零係数の線形な余単体 cochain の正次数コホモロジーの消滅。
方針：交代余面複体と非斉次 cochain 複体の実際の同型で平均化による消滅を移す。
規約：この宣言は代数的 cochain のコホモロジーの主張であり Tot の π_* の主張を含まない。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の cochain 計算の入力。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Spectra.LinearGroupCochains

/-- 概要：有限群の標数零の線形な非斉次余単体 cochain の正次数コホモロジーは零。
方針：群コホモロジーとの比較同型に平均化からの消滅を適用する。
規約：零次数の消滅は主張しない。
使われ方：Goerss–Jardine VIII §2。Tot のホモトピー群の計算に必要な代数的な消滅。 -/
theorem positive_cohomology_isZero {k G : Type u} [Field k] [CharZero k]
    [Group G] [Finite G] (A : Rep.{u} k G) (n : ℕ) :
    IsZero ((complex A).homology (n + 1)) :=
  (rationalGroupCohomology_isZero A n).of_iso (cohomologyIso A (n + 1))

end SerrePositivity.KST.Spectra.LinearGroupCochains
