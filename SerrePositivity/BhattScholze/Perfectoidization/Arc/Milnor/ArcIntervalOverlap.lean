module

public import SerrePositivity.CommutativeAlgebra.ValuationInterval.Basic
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcMilnorTensor

/-!
## 概要
重なる区間での係数の短完全列（BM18 Proposition 4.8 の証明の図式 (6)）。
## 方針
上端での局所化と下端での商を、交わりの区間環で比較する。
## 規約
局所化から区間環への制限は全射。差は加群の線形写像とする。
## 使われ方
完全代数をテンソルし、重なりを持つ区間への制限で Čech 完全性を検出する。
-/

@[expose] public noncomputable section

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V]
variable {a b : PrimeSpectrum V} (h : a ≤ b)

theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.intervalRing_algebraMap_eq_zero_iff (x : V) :
    algebraMap V (_root_.SerrePositivity.ValuationIntervalRing h) x = 0 ↔ x ∈ a.asIdeal := by
  rw [IsScalarTower.algebraMap_apply V (V ⧸ a.asIdeal)]
  have hi : Function.Injective (algebraMap (V ⧸ a.asIdeal) (_root_.SerrePositivity.ValuationIntervalRing h)) :=
    IsLocalization.injective _ (M := (_root_.SerrePositivity.intervalPrime h).primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  exact ⟨fun hz => Ideal.Quotient.eq_zero_iff_mem.mp (hi (hz.trans (map_zero _).symm)),
    fun hx => _root_.SerrePositivity.intervalRing_map_eq_zero h hx⟩

/-- 局所化から閉区間への制限射（BM18 Proposition 4.8 の証明の図式 (6)）。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval : Localization.AtPrime b.asIdeal →ₐ[V] _root_.SerrePositivity.ValuationIntervalRing h where
  __ := IsLocalization.lift (M := b.asIdeal.primeCompl) (g := algebraMap V _)
    (fun s => _root_.SerrePositivity.intervalRing_isUnit h s.2)
  commutes' x := IsLocalization.lift_eq (M := b.asIdeal.primeCompl) _ x

theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval_surjective :
    Function.Surjective (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h) := by
  let f := Ideal.Quotient.mk a.asIdeal
  have hm : b.asIdeal.primeCompl.map f = (_root_.SerrePositivity.intervalPrime h).primeCompl := by
    have he (x : V) : f x ∈ (_root_.SerrePositivity.intervalPrime h).primeCompl ↔ x ∈ b.asIdeal.primeCompl := by
      change f x ∉ _root_.SerrePositivity.intervalPrime h ↔ x ∉ b.asIdeal
      rw [← Ideal.mem_comap, _root_.SerrePositivity.intervalPrime_comap]
    ext y
    rw [Submonoid.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (he x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, (he x).mp hy, rfl⟩
  let : IsLocalization (b.asIdeal.primeCompl.map f) (_root_.SerrePositivity.ValuationIntervalRing h) :=
    hm.symm ▸ inferInstance
  let g : Localization.AtPrime b.asIdeal →+* _root_.SerrePositivity.ValuationIntervalRing h :=
    IsLocalization.map (_root_.SerrePositivity.ValuationIntervalRing h) f (M := b.asIdeal.primeCompl)
      (T := b.asIdeal.primeCompl.map f) (fun s hs => ⟨s, hs, rfl⟩)
  have hsurj : Function.Surjective (g : Localization.AtPrime b.asIdeal →+* _) :=
    IsLocalization.map_surjective_of_surjective _ _ _ Ideal.Quotient.mk_surjective
  have he : (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h).toRingHom = g := by
    apply IsLocalization.ringHom_ext b.asIdeal.primeCompl
    apply RingHom.ext
    intro x
    exact ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h).commutes x).trans
      (IsLocalization.map_eq (S := Localization.AtPrime b.asIdeal)
        (Q := _root_.SerrePositivity.ValuationIntervalRing h) (g := f) (M := b.asIdeal.primeCompl)
        (T := b.asIdeal.primeCompl.map f) (fun s hs => ⟨s, hs, rfl⟩) x).symm
  change Function.Surjective (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h).toRingHom
  rw [he]
  exact hsurj

/-- 重なる二つの区間に制限する短複体（BM18 Proposition 4.8 の証明の図式 (6)）。 -/
def _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex : ShortComplex (ModuleCat.{u} V) :=
  ShortComplex.moduleCatMk
    ((Algebra.linearMap V (Localization.AtPrime b.asIdeal)).prod
      (Algebra.linearMap V (V ⧸ a.asIdeal)))
    ((_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h).toLinearMap.comp (LinearMap.fst V _ _) -
      ((Algebra.linearMap (V ⧸ a.asIdeal) (_root_.SerrePositivity.ValuationIntervalRing h)).restrictScalars V).comp
        (LinearMap.snd V _ _)) (by
    apply LinearMap.ext
    intro x
    change _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h (algebraMap V _ x) -
      algebraMap (V ⧸ a.asIdeal) (_root_.SerrePositivity.ValuationIntervalRing h) (Ideal.Quotient.mk a.asIdeal x) = 0
    rw [(_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h).commutes]
    exact sub_self _)

/-- 重なる二つの区間に対する係数の短完全列
（BM18 Proposition 4.8 の証明の図式 (6)）。 -/
theorem _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex_shortExact [IsDomain V] [ValuationRing V] :
    (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.overlapModuleComplex h).ShortExact := by
  let L := Localization.AtPrime b.asIdeal
  let f := algebraMap V L
  let r := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval h
  have hf : Function.Injective f :=
    IsLocalization.injective _ (M := b.asIdeal.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors _)
  have hkernel (x : L) (hx : r x = 0) : ∃ v ∈ a.asIdeal, f v = x := by
    obtain ⟨v, s, rfl⟩ := IsLocalization.exists_mk'_eq b.asIdeal.primeCompl x
    have he := congrArg r (IsLocalization.mk'_spec L v s)
    rw [map_mul, hx, zero_mul, r.commutes] at he
    have hv := (_root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.intervalRing_algebraMap_eq_zero_iff h v).mp he.symm
    have hsa : (s : V) ∉ a.asIdeal := fun hs => s.2 (h hs)
    rcases ValuationRing.dvd_total (s : V) v with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hw' := (a.isPrime.mem_or_mem (hw ▸ hv)).resolve_left hsa
      exact ⟨w, hw', IsLocalization.eq_mk'_iff_mul_eq.mpr (by rw [hw, map_mul, mul_comm])⟩
    · exact (hsa (hw ▸ a.asIdeal.mul_mem_right w hv)).elim
  apply ModuleCat.shortComplex_shortExact
  · rintro ⟨x, y⟩
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
    change r x - algebraMap (V ⧸ a.asIdeal) (_root_.SerrePositivity.ValuationIntervalRing h)
      (Ideal.Quotient.mk a.asIdeal v) = 0 ↔ _
    constructor
    · intro hx
      have hsub : r (x - f v) = 0 := by
        rw [map_sub, r.commutes]
        exact hx
      obtain ⟨w, hw, hwe⟩ := hkernel _ hsub
      refine ⟨w + v, Prod.ext ?_ ?_⟩
      · change f (w + v) = x
        rw [map_add, hwe, sub_add_cancel]
      · change Ideal.Quotient.mk a.asIdeal (w + v) = Ideal.Quotient.mk a.asIdeal v
        rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hw, zero_add]
    · rintro ⟨w, he⟩
      have h₁ : f w = x := congrArg Prod.fst he
      have h₂ : Ideal.Quotient.mk a.asIdeal w = Ideal.Quotient.mk a.asIdeal v :=
        congrArg Prod.snd he
      rw [← h₁, ← h₂, r.commutes]
      exact sub_self _
  · exact fun _ _ he => hf (congrArg Prod.fst he)
  · intro z
    obtain ⟨x, hx⟩ := _root_.SerrePositivity.BhattScholze.Perfectoidization.Arc.localizationToInterval_surjective h z
    refine ⟨(x, 0), ?_⟩
    change r x - (algebraMap (V ⧸ a.asIdeal) (_root_.SerrePositivity.ValuationIntervalRing h)) 0 = z
    rw [map_zero, sub_zero, hx]

end SerrePositivity.BhattScholze.Perfectoidization.Derived
