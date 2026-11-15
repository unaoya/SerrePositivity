module

public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcIntervalOverlap

/-!
## 概要
重なる二つの区間と交わりによる Čech 完全性の検出。
## 方針
係数の短完全列を、Tor 消滅を使って増大 Čech 複体の各項でテンソルする。
## 規約
区間の和を全スペクトルに正規化して述べる。
## 使われ方
BM18 Proposition 4.8 の証明 (5) の図式 (6) を構造層に適用する。
-/

@[expose] public noncomputable section

universe u
open _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

/-- 重なる二つの区間とその交わりの三つの底変換で Čech 完全性を検出する。
区間は下端が零の区間と上端が極大の区間に正規化している
（BM18 Proposition 4.8 の証明の図式 (6)）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_of_overlapTensor {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    {a b : PrimeSpectrum V} (h : a ≤ b)
    (B : Under (CommRingCat.of V)) (p : ℕ) [Fact p.Prime]
    [PerfectRing V p] [PerfectRing B.right p] (hp : (p : V) = 0)
    (hl : _root_.SerrePositivity.Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of (Localization.AtPrime b.asIdeal))).obj B).hom))
    (hq : _root_.SerrePositivity.Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of (V ⧸ a.asIdeal))).obj B).hom))
    (hr : _root_.SerrePositivity.Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of (_root_.SerrePositivity.ValuationIntervalRing h))).obj B).hom)) :
    _root_.SerrePositivity.Cech.IsCechExact (Arrow.mk B.hom) := by
  let K := _root_.SerrePositivity.Cech.moduleCech B
  let S := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex h
  let : PerfectRing (_root_.SerrePositivity.ValuationIntervalRing h) p := _root_.SerrePositivity.perfectRing_interval h p hp
  have h₁ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.acyclic_of_tensorShortExact K S (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex_shortExact h)
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.moduleCech_tor_subsingleton B (_root_.SerrePositivity.ValuationIntervalRing h) p hp 1 (by decide))
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_prod_acyclic K _ _
      ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_baseChange_iff_tensorCochain B _).mp hl)
      ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_baseChange_iff_tensorCochain B _).mp hq))
    ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.cechExact_baseChange_iff_tensorCochain B _).mp hr)
  exact (_root_.SerrePositivity.Cech.moduleCech_acyclic_iff B).mp (fun n => (h₁ n).of_iso (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.tensorCochain_unitIso K))

end SerrePositivity.BhattScholze.Perfectoidization.Derived
