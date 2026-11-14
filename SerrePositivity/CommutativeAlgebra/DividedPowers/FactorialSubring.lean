module
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.RingTheory.OreLocalization.Basic
public import Mathlib.GroupTheory.OreLocalization.OreSet
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Algebra.Defs

public import SerrePositivity.CommutativeAlgebra.FlatRegularQuotient
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal
public import Mathlib.RingTheory.WittVector.Identities
public import Mathlib.RingTheory.Regular.Flat

/-!
# 階乗分母で生成される部分環

既存の構成とその型・証明を保ち、必要な下位の依存だけを用いる。
-/

universe u v w z

/-! ## 最初の実p除算関係と通常商のp正則性

任意の指定変数sについて、δ閉包前の一つの実関係式を扱う。
全δ関係商・完備化・分冪包の平坦性は結論しない。
-/

@[expose] public noncomputable section DeltaPDivisionFactorialSubring

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- A[1/p]内の正規化されたy_s^n/n!。非p倍の単元性は利用時に明示する。 -/
def pDivisionFactorialValue (p : ℕ) (y : σ → A) (s : σ) (n : ℕ) :
    Localization.Away (p : A) :=
  Ring.inverse (n.factorial : Localization.Away (p : A)) *
    (algebraMap A (Localization.Away (p : A)) (y s)) ^ n

/-- Aとすべての階乗分母y_s^n/n!で生成される具体的な局所化内部分環。 -/
def pDivisionFactorialSubring (p : ℕ) (y : σ → A) : Subring (Localization.Away (p : A)) :=
  Subring.closure (Set.range (algebraMap A (Localization.Away (p : A))) ∪
    Set.range (fun z : σ × ℕ ↦ pDivisionFactorialValue p y z.1 z.2))

omit [Fact p.Prime] in
/-- 元のAの像は階乗生成部分環に入る。 -/
theorem pDivisionFactorialSubring_coeff_mem (y : σ → A) (r : A) :
    algebraMap A (Localization.Away (p : A)) r ∈ pDivisionFactorialSubring p y :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

omit [Fact p.Prime] in
/-- 正規化された各階乗分母は、定義した生成部分環に入る。 -/
theorem pDivisionFactorialSubring_value_mem (y : σ → A) (s : σ) (n : ℕ) :
    pDivisionFactorialValue p y s n ∈ pDivisionFactorialSubring p y :=
  Subring.subset_closure (Or.inr ⟨(s, n), rfl⟩)

end SerrePositivity.BhattScholze

end DeltaPDivisionFactorialSubring

/-! ## 実局所化δ構造での階乗生成元の展開

環同型に沿った別のδ作用ではなく、既存の局所化δ作用を直接計算する。
-/

