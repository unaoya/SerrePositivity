module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.Homotopy

/-!
# 非正次数の複体のホモトピーの制限

## 概要
HA 3.2.4.7 の係数比較で使う、q ↦ −q に沿った実際のホモトピーの制限。

## 方針
ホモトピーの各成分を制限し、零次の境界では元の複体の正一次が零であることを使う。

## 規約
元の指定された順射・逆射とホモトピーの成分を保つ。

## 使われ方
二色のテンソル係数の増大の鎖ホモトピー同値性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  {K L : CochainComplex C ℤ}

/-- 正一次が零である始域からのホモトピーは、非負の鎖次数へ制限できる。 -/
def nonpositiveHomotopyRestriction {f g : K ⟶ L} (h : Homotopy f g)
    (hK : IsZero (K.X 1)) :
    Homotopy (restrictionMap f ComplexShape.embeddingDownNat)
      (restrictionMap g ComplexShape.embeddingDownNat) where
  hom i j := h.hom (-(i : ℤ)) (-(j : ℤ))
  zero i j hij := by
    apply h.zero
    change ¬ (-(j : ℤ) + 1 = -(i : ℤ))
    change ¬ (i + 1 = j) at hij
    omega
  comm i := by
    cases i with
    | zero =>
      have hh := h.comm (0 : ℤ)
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)] at hh
      rw [dNext_eq_zero _ 0 (by decide),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel 1 0 by decide)]
      change f.f 0 = 0 + h.hom 0 (-1) ≫ L.d (-1) 0 + g.f 0
      have hz : K.d 0 1 = 0 := hK.eq_of_tgt _ _
      simpa only [hz, zero_comp] using hh
    | succ i =>
      rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (i + 1) i by rfl),
        prevD_eq _ (show (ComplexShape.down ℕ).Rel (i + 2) (i + 1) by rfl)]
      have hh := h.comm (-((i + 1 : ℕ) : ℤ))
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) by
          change -((i + 1 : ℕ) : ℤ) + 1 = -(i : ℤ)
          omega),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-((i + 2 : ℕ) : ℤ))
          (-((i + 1 : ℕ) : ℤ)) by
          change -((i + 2 : ℕ) : ℤ) + 1 = -((i + 1 : ℕ) : ℤ)
          omega)] at hh
      exact hh

/-- 双方の正一次が零である複体間の指定同値を、非負の鎖複体へ制限する。 -/
def nonpositiveHomotopyEquivRestriction (e : HomotopyEquiv K L)
    (hK : IsZero (K.X 1)) (hL : IsZero (L.X 1)) :
    HomotopyEquiv (K.restriction ComplexShape.embeddingDownNat)
      (L.restriction ComplexShape.embeddingDownNat) where
  hom := restrictionMap e.hom ComplexShape.embeddingDownNat
  inv := restrictionMap e.inv ComplexShape.embeddingDownNat
  homotopyHomInvId := by
    simpa only [restrictionMap_comp, restrictionMap_id] using
      nonpositiveHomotopyRestriction e.homotopyHomInvId hK
  homotopyInvHomId := by
    simpa only [restrictionMap_comp, restrictionMap_id] using
      nonpositiveHomotopyRestriction e.homotopyInvHomId hL

end SerrePositivity.EInfinity
