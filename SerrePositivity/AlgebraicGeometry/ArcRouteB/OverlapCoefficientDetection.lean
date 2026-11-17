module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapShortExact
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcCechMilnor

/-!
概要：重なる区間の三つの底変換で、任意の完全係数の増大Čech完全性を検出する。
方針：L01/L02で同じArrowを保って係数を比較し、T上の短完全列とTor消滅をmoduleCechへ適用する。
規約：係数Tの平坦性は仮定しない。単なる完全性を非平坦底変換へ保存したことにしない。
使われ方：2iのO06、BM18 Proposition 4.8(5)の構造層に特殊化した普遍貼り合わせ。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
open SerrePositivity.BhattScholze.Perfectoidization
open scoped TensorProduct
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- L05：同じT上の重なりの短完全列で、三つの係数上のČech完全性を検出する。 -/
theorem cechExact_of_overlapTensor_coefficients (p : ℕ) [Fact p.Prime]
    {V T : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing T] [Algebra V T] [PerfectRing V p] [PerfectRing T p]
    (B : Under (CommRingCat.of T)) [PerfectRing B.right p] (hp : (p : V) = 0)
    {a b : PrimeSpectrum V} (h : a ≤ b)
    (hl : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] Localization.AtPrime b.asIdeal))).obj B).hom))
    (hq : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] (V ⧸ a.asIdeal)))).obj B).hom))
    (hr : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of T)
      (CommRingCat.of (T ⊗[V] ValuationIntervalRing h))).obj B).hom)) :
    Cech.IsCechExact (Arrow.mk B.hom) := by
  let L := Localization.AtPrime b.asIdeal
  let Q := V ⧸ a.asIdeal
  let I := ValuationIntervalRing h
  let K := Cech.moduleCech B
  have hT : (p : T) = 0 := by rw [← map_natCast (algebraMap V T), hp, map_zero]
  letI : PerfectRing I p := perfectRing_interval h p hp
  letI : PerfectRing (T ⊗[V] I) p := perfectTensor_of_primeCast_eq_zero p V T I hp
  let S := overlapTensorModuleComplex (T := T) h
  have hs : S.ShortExact := overlapTensorModuleComplex_shortExact p hp h
  have hleft := (Arc.cechExact_baseChange_iff_tensorCochain B (T ⊗[V] L)).mp hl
  have hquot := (Arc.cechExact_baseChange_iff_tensorCochain B (T ⊗[V] Q)).mp hq
  have hinter := (Arc.cechExact_baseChange_iff_tensorCochain B (T ⊗[V] I)).mp hr
  have hunit := Arc.acyclic_of_tensorShortExact K S hs
    (Arc.moduleCech_tor_subsingleton B (T ⊗[V] I) p hT 1 (by decide))
    (Arc.tensorCochain_prod_acyclic K (T ⊗[V] L) (T ⊗[V] Q) hleft hquot) hinter
  exact (Cech.moduleCech_acyclic_iff B).mp
    (fun n ↦ (hunit n).of_iso (Arc.tensorCochain_unitIso K))

end SerrePositivity.AlgebraicGeometry.ArcRouteB
