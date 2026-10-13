module

public import SerrePositivity.Spectra.PointedSimplicialSet.Basic
public import SerrePositivity.Spectra.Pointed.AdjoinBasepoint
public import SerrePositivity.Spectra.Pointed.Cofiber
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# 境界を潰して得る基点付き単体的球面

標準 n 単体の境界を一つの点へ潰す通常の pushout として、球面を定義する。
特に単体的な円は Δ[1]/∂Δ[1] であり、今後のスペクトルの構造写像に使う。
この商の普遍性は一般の `PointedObject.cofiberHomEquiv` で証明済み。
球面のホモトピー群、自由な基点による零次球面との比較、モデル構造はまだ扱わない。
-/

@[expose] public section

universe u

namespace SerrePositivity.PointedSimplicialSet

open CategoryTheory
open scoped Simplicial

/-- 標準単体の境界を基点へ潰した単体的球面。 -/
noncomputable def sphere (n : ℕ) : PointedSimplicialSet.{u} :=
  PointedObject.cofiber (SSet.boundary.{u} n).ι

/-- 単体的な円。球面の一次元の場合を使う。 -/
noncomputable abbrev circle : PointedSimplicialSet.{u} := sphere 1

/-- smash 積の単位に用いる、自由な基点を持つ零次球面。 -/
noncomputable abbrev sphereZero : PointedSimplicialSet.{u} := PointedObject.sphereZero

end SerrePositivity.PointedSimplicialSet
