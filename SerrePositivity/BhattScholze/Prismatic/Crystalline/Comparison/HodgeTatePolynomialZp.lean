module
public import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCompletedMap
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Affine.HodgeTateCartierAssembly
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineBase
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Algebra.Ring.ULift

import all SerrePositivity.CommutativeAlgebra.DeRham.UniversalProperty

/-!
# 結晶 prism 上の多項式の Hodge–Tate 比較

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial SerrePositivity.DeRham
open scoped Simplicial TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => crystallineBasePrism p
local notation "hZ" => crystallineBaseBounded p
local notation "k" => cartierBase p
local notation "T" => formVars r
local notation "Φ" => finitePolynomialCartier p r
local notation "η" => hodgeTateMap Z hZ r
local notation "Ψ" => crystallineChain p r

/-- Bhatt–Scholze Corollary 5.5 の結晶基底 `(ℤ_p,(p))` の多項式の場合。 -/
theorem hodgeTate_iso_polynomial_Zp :
    HodgeTateIsoStatement (crystallineBasePrism.{u} p) (crystallineBaseBounded p) r :=
  hodgeTate_of_deRham_cartier p r

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 5.5" (partial := special) "結晶基底 (Z_p,(p)) の多項式の場合を de Rham 比較と inverse Cartier で直接証明（D68 改訂、BS-D68 停止点 3）。一般の結晶 prism 上の S = A/p[X]（Lemma 4.20 で帰着）は drafts ／ 11-10 更新（2）"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp
attribute [cite BS19 "Thm 4.11" (partial := component) "主張の型（HodgeTateIsoStatement）と結晶基底 (Z_p,(p)) の場合は本体（BS-D68）。一般の有界向き付き基底への帰着（Prop 6.2・Thm 6.3）は drafts ／ 11-10 更新（2）。本体の HodgeTateIsoStatement は Rem 4.19 の鎖複体の模型（reducedModel）のコホモロジーについての主張で、site の RΓ ではない ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.hodgeTate_iso_polynomial_Zp
