module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FiniteStability
import SerrePositivity.AlgebraicGeometry.NoetherianFiberComponent
import Mathlib.Tactic.Ring

/-!
概要：局所化上の冪等元を一つの元を反転した段に降ろす。
方針：分母を払って得られる冪等性の関係式を、分母を一つ追加して成立させる。
規約：局所化は可換環の乗法部分モノイドで行う。
使われ方：生成ファイバーの開閉部分を基底の主開集合上に広げる。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

/--
概要：局所化上の冪等元は一つの分母を反転した環の冪等元から来る。
方針：冪等性の関係式の分母を払う。
規約：選ぶ分母は元の乗法部分モノイドに属する。
使われ方：一般ファイバーの開閉部分を主開集合上に広げる。
-/
theorem exists_idempotent_away_of_isLocalization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (d : S) (hd : IsIdempotentElem d) :
    ∃ (r : M) (e : Localization.Away (r : R)), IsIdempotentElem e ∧
      IsLocalization.Away.lift (g := algebraMap R S) (r : R)
        (IsLocalization.map_units S r) e = d := by
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq M d
  let d := IsLocalization.mk' S b s
  change IsIdempotentElem d at hd
  change ∃ (r : M) (e : Localization.Away (r : R)), IsIdempotentElem e ∧
    IsLocalization.Away.lift (g := algebraMap R S) (r : R)
      (IsLocalization.map_units S r) e = d
  have hbs : d * algebraMap R S (s : R) = algebraMap R S b :=
    IsLocalization.mk'_spec S b s
  have hab : algebraMap R S (b * b) = algebraMap R S ((s : R) * b) := by
    rw [map_mul, map_mul, ← hbs]
    calc
      _ = (d * d) * (algebraMap R S (s : R) * algebraMap R S (s : R)) := by ring
      _ = _ := by rw [hd.eq]; ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists M S).mp hab
  let r := s * t
  let c := (t : R) * b
  have hc : c * c = (r : R) * c := by
    calc
      c * c = (t : R) * ((t : R) * (b * b)) := by dsimp [c]; ring
      _ = (t : R) * ((t : R) * ((s : R) * b)) := by rw [ht]
      _ = (r : R) * c := by dsimp [r, c]; ring
  let C := Localization.Away (r : R)
  let v : Submonoid.powers (r : R) := ⟨r, Submonoid.mem_powers _⟩
  let e := IsLocalization.mk' C c v
  have hec : e * algebraMap R C (r : R) = algebraMap R C c :=
    IsLocalization.mk'_spec C c v
  have hu : IsUnit (algebraMap R C (r : R)) := IsLocalization.map_units C v
  refine ⟨r, e, ?_, ?_⟩
  · apply (hu.mul hu).mul_left_inj.mp
    calc
      (e * e) * (algebraMap R C (r : R) * algebraMap R C (r : R)) =
          (e * algebraMap R C (r : R)) * (e * algebraMap R C (r : R)) := by ring
      _ = algebraMap R C (c * c) := by
        rw [hec]
        exact (map_mul (algebraMap R C) c c).symm
      _ = algebraMap R C (r : R) * (e * algebraMap R C (r : R)) := by
        rw [hc, map_mul, hec]
      _ = e * (algebraMap R C (r : R) * algebraMap R C (r : R)) := by ring
  · let hunit := IsLocalization.map_units S r
    let j : C →+* S := IsLocalization.Away.lift (r : R) hunit
    change j e = d
    apply hunit.mul_left_inj.mp
    calc
      j e * algebraMap R S (r : R) = j (e * algebraMap R C (r : R)) := by
        rw [map_mul, IsLocalization.Away.lift_eq (r : R) hunit]
      _ = algebraMap R S c := by rw [hec, IsLocalization.Away.lift_eq (r : R) hunit]
      _ = d * algebraMap R S (r : R) := by
        dsimp [c, r]
        rw [map_mul, map_mul, ← hbs]
        ring

open scoped TensorProduct nonZeroDivisors

/--
概要：有限型アフィン射の一般ファイバーの連結成分は、基底の非零元を一つ反転した上の
開閉部分の逆像になる。
方針：連結成分を冪等元で表し、基底の分母を一つ選んでその冪等元を降ろす。
規約：基底は整域とし、一般ファイバーは分数体へのテンソル積で表す。
使われ方：Stacks 055N の一般ファイバーにおける開閉分解。
-/
theorem exists_clopen_away_of_generic_fiber_component
    {A B K : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [Field K] [Algebra A K] [IsFractionRing A K]
    (x : PrimeSpectrum (B ⊗[A] K)) :
    ∃ (a : A) (ha : a ∈ A⁰) (U : Set (PrimeSpectrum (Localization.Away (algebraMap A B a)))),
      IsClopen U ∧
      (PrimeSpectrum.comap (IsLocalization.Away.lift
        (g := algebraMap B (B ⊗[A] K)) (algebraMap A B a)
        (IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] K)
          ⟨algebraMap A B a, ⟨a, ha, rfl⟩⟩))) ⁻¹' U =
        connectedComponent x := by
  let : Algebra K (B ⊗[A] K) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.FiniteType K (B ⊗[A] K) :=
    Algebra.FiniteType.equiv inferInstance (Algebra.TensorProduct.commRight A K B)
  let : IsNoetherianRing (B ⊗[A] K) := Algebra.FiniteType.isNoetherianRing K _
  obtain ⟨d, hd, hdx⟩ := PrimeSpectrum.isClopen_iff.mp
    (isClopen_connectedComponent_of_noetherianSpace x)
  obtain ⟨⟨r, hr⟩, e, he, hed⟩ :=
    exists_idempotent_away_of_isLocalization (Algebra.algebraMapSubmonoid B A⁰) d hd
  obtain ⟨a, ha, rfl⟩ := hr
  refine ⟨a, ha, PrimeSpectrum.basicOpen e, PrimeSpectrum.isClopen_iff.mpr ⟨e, he, rfl⟩, ?_⟩
  rw [hdx]
  exact congrArg (fun z => (PrimeSpectrum.basicOpen z : Set (PrimeSpectrum (B ⊗[A] K)))) hed

end SerrePositivity.AlgebraicGeometry
