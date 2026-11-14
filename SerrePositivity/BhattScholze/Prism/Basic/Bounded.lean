module
public import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Group.Monoid

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# 向き付き prism の有界性

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory
open scoped Cardinal

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime]

/-! ## 有界 prism -/

/-- 概要：向き付き prism が有界：A/d の p 冪ねじれが一様な冪 p^N で消える（原典 Def 3.2 の「有界」）。
方針：既存の有界性の仮定（`Prism/Bounded/Completeness` の `hB`）をそのまま述語にする。
規約：A 自身の p ねじれには触れない。
使われ方：site の対象の条件、Lemma 3.7。 -/
def IsBoundedPrism {A : Type u} [CommRing A] (P : OrientedPrism p A) : Prop :=
  ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ P.ideal),
    (p : A ⧸ P.ideal) ^ n * x = 0 → (p : A ⧸ P.ideal) ^ N * x = 0

end SerrePositivity.BhattScholze.Prismatic

/-! Reviewed literature correspondences. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Def 1.4"] _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism
attribute [cite BS19 "Def 3.2" (partial := special) "向き付き prism（単項イデアルと生成元をデータに）に限る（D5・D19）。有界性の述語 IsBoundedPrism は本体（Prismatic/PrismOver） ／ DOC1 照合：ok 2 件"] _root_.SerrePositivity.BhattScholze.Prismatic.IsBoundedPrism
