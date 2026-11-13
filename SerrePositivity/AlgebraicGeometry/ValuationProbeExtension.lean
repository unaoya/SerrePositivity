module

public import SerrePositivity.CommutativeAlgebra.ValuationExtension.Aic

/-!
概要：付値整域から体への単射を、忠実平坦な付値環拡大に分解する。
方針：局所環から体への射を支配する付値部分環を取り、単射な局所準同型の忠実平坦性を使う。
規約：体と環は同じ宇宙。元の付値環の整域構造を保持する。
使われ方：G0 の flat・proper な射の付値持ち上げ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {V R K : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable [CommRing R] [IsLocalRing R] [Field K]

/-- 付値基底上で単射となる体への射は、忠実平坦な付値環拡大を通して因子化する。 -/
theorem exists_valuationSubring_factor_of_injective_local_base
    (a : V →+* R) [IsLocalHom a] (f : R →+* K)
    (ha : Function.Injective (f.comp a)) :
    ∃ (W : ValuationSubring K) (b : R →+* W),
      IsLocalHom b ∧ (algebraMap W K).comp b = f ∧ (b.comp a).FaithfullyFlat := by
  obtain ⟨W, hW, hb⟩ := IsLocalRing.exists_factor_valuationRing f
  let b : R →+* W := f.codRestrict W.toSubring hW
  letI : IsLocalHom b := hb
  refine ⟨W, b, hb, rfl, ?_⟩
  apply SerrePositivity.faithfullyFlat_of_injective_local_valuation (b.comp a)
  intro x y hxy
  exact ha (congrArg (fun z : W ↦ (z : K)) hxy)

/-- 体への単射から得る、同じ体の付値部分環への忠実平坦な拡大。 -/
theorem exists_valuationSubring_extension_of_injective (i : V →+* K)
    (hi : Function.Injective i) :
    ∃ (W : ValuationSubring K) (e : V →+* W),
      (algebraMap W K).comp e = i ∧ e.FaithfullyFlat := by
  obtain ⟨W, e, _, he, hf⟩ :=
    exists_valuationSubring_factor_of_injective_local_base (RingHom.id V) i hi
  exact ⟨W, e, he, by simpa only [RingHom.comp_id] using hf⟩

end SerrePositivity.AlgebraicGeometry
