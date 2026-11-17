module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalGluing
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.LocalExtensions
public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Zorn
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
public import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
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

/-- 計画I11：有限表示代数の完全化のarc被覆は、任意の完全係数でČech完全。 -/
theorem perfectedFpArc_universalExact (p : ℕ) [Fact p.Prime]
    {V C : Type u} [CommRing V] [IsDomain V] [ValuationRing V] [CommRing C]
    [Algebra V C] [Algebra.FinitePresentation V C] [PerfectRing V p]
    (hV : IsAbsolutelyIntegrallyClosed V) (hp : (p : V) = 0)
    (hf : IsArcHom (perfectedAlgebraUnit p V C hp)) :
    PerfectRingCechUniversalExact p (perfectedAlgebraUnit p V C hp) := by
  let hC : (p : C) = 0 := by rw [← map_natCast (algebraMap V C), hp, map_zero]
  let CP := FrobeniusDirectLimit C p (Fact.out : p.Prime) hC
  letI : PerfectRing CP p := frobeniusDirectLimit_perfectRing p C hC
  let f := perfectedAlgebraUnit p V C hp
  have hall {a b : PrimeSpectrum V} (hab : a ≤ b) : GoodArcInterval p f a b := by
    apply valuationIntervalProperty_of_localExtensions (GoodArcInterval p f) ?_ ?_ ?_ ?_ ?_ hab
    · intro a
      exact goodArcInterval_of_rank_le_one p hp f hf le_rfl
        (intervalRing_krullDim_le_one_of_no_prime_between le_rfl
          (fun c hac hca ↦ Or.inl (le_antisymm hca hac)))
    · intro a b c d hg hac hcd hdb
      letI : PerfectRing (ValuationIntervalRing hcd) p := perfectRing_interval hcd p hp
      exact goodArcInterval_sub p f hg hac hcd hdb
    · exact fun hab ↦ goodArcInterval_right p hV hp hf hab
    · exact fun hab ↦ goodArcInterval_left p hV hp hf hab
    · exact fun hac hcb hbd h₁ h₂ ↦ goodArcInterval_glue p hp f hac hcb hbd h₁ h₂
  let a : PrimeSpectrum V := ⟨⊥, inferInstance⟩
  let b : PrimeSpectrum V := ⟨IsLocalRing.maximalIdeal V, inferInstance⟩
  have hab : a ≤ b := bot_le
  let e := intervalRingOfFullSpectrumEquiv a b rfl rfl hab
  intro T _ _ k
  have he : (k.comp e.toRingHom).comp (algebraMap V (ValuationIntervalRing hab)) = k := by
    apply RingHom.ext
    intro v
    exact congrArg k (e.commutes v)
  let q := arcBaseChangeTransIso f (algebraMap V (ValuationIntervalRing hab))
    (k.comp e.toRingHom) k he
  exact (Cech.ringCechExact_iff_of_iso
    (CosimplicialObject.augmentedCechConerve.mapIso q)).mpr (hall hab hab T (k.comp e.toRingHom))

end SerrePositivity.AlgebraicGeometry.ArcRouteB
