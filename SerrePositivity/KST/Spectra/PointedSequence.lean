module

public import SerrePositivity.KST.Spectra.SuspensionLoop

/-!
概要：Kan 性を要求しない点つき単体集合のスペクトル列。
方針：各段と suspension 構造射を持たせる。
規約：単射性も Ω 条件も要求しない。
使われ方：BF 1978 §2、HTT A.3.3。段ごとの Kan 置換の入力。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace SerrePositivity.KST.Spectra

/-- 概要：点つき単体集合の suspension 構造射付きの列。
方針：各段を通常の点つき対象として持つ。
規約：まだ Kan 性を要求しない。
使われ方：BF 1978 §2、HTT A.3.3。Kan 置換前の列。 -/
structure PointedSequence where
  /-- 概要：列の各段。
  方針：点つき単体集合を使う。
  規約：自然数の添字。
  使われ方：BF 1978 §2。 -/
  level : ℕ → PointedSimplicialSet.{u}
  /-- 概要：suspension の構造射。
  方針：円との smash からの射で与える。
  規約：任意の点つき射。
  使われ方：BF 1978 §2。 -/
  sigma : ∀ n, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (level n) ⟶ level (n + 1)

namespace PointedSequence

/-- 概要：点つき列の厳密な射。
方針：各段の射と構造射との厳密可換性を与える。
規約：Kan 性は要求しない。
使われ方：BF 1978 §2。Kan 置換への比較射。 -/
structure Hom (X Y : PointedSequence.{u}) where
  /-- 概要：各段の射。
  方針：点つき射を使う。
  規約：同じ段の間。
  使われ方：BF 1978 §2。 -/
  app : ∀ n, X.level n ⟶ Y.level n
  /-- 概要：構造射との厳密な可換式。
  方針：suspension の射への作用を使う。
  規約：各自然数の段での等式。
  使われ方：BF 1978 §2。 -/
  comm : ∀ n, PointedSimplicialSet.circle.{u} ◁ app n ≫ Y.sigma n =
    X.sigma n ≫ app (n + 1)

end PointedSequence

end SerrePositivity.KST.Spectra
