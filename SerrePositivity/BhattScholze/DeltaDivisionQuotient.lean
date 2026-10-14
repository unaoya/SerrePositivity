module

public import SerrePositivity.BhattScholze.DeltaDivisionUniversal

/-! # 除算添加後のmod dへの商射

著者公開版Prop 7.2のR→Δ/dがSを経由する代数的な計算。
Rの任意のイデアルJの全元をdで割る添加環と旧ねじれ除去商に対し、
R/Jからmod dへの標準環射を構成する。完備性は仮定せず、prismとは呼ばない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 除算添加・旧ねじれ除去の後も各a_sの像はdの像で割り切れる。 -/
theorem deltaDivisionTorsionMap_dvd {σ : Type*}
    (D : DeltaStructure p R) (d : R) (a : σ → R) (s : σ) :
    deltaDivisionTorsionMap D d a d ∣ deltaDivisionTorsionMap D d a (a s) := by
  let q : DeltaAdjoinDivision D d a →+* DeltaDivisionTorsionQuotient D d a :=
    Ideal.Quotient.mk _
  refine ⟨q (deltaAdjoinDivisionVariable D d a s), ?_⟩
  have h := congrArg q (deltaAdjoinDivision_relation D d a s)
  rw [map_mul] at h
  exact h.symm

/-- イデアルJの全元をdで割る二段階商で、Jの像はdの像の主イデアルに含まれる。 -/
theorem deltaDivisionTorsionMap_ideal_le_span (D : DeltaStructure p R) (d : R)
    (J : Ideal R) :
    J ≤ (Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}).comap
      (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R))) := by
  intro x hx
  change deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) x ∈
    Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}
  apply Ideal.mem_span_singleton.mpr
  exact deltaDivisionTorsionMap_dvd D d (fun x : J ↦ (x : R)) ⟨x, hx⟩

/-- Jの全元をdで割った後、mod dへの基底射はR/Jを経由する。
任意の商Jを扱い、pねじれや導来・古典的完備性を追加仮定しない。 -/
def deltaDivisionQuotientMap (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    R ⧸ J →+*
      (DeltaDivisionTorsionQuotient D d (fun x : J ↦ (x : R)) ⧸
        Ideal.span {deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) d}) :=
  Ideal.Quotient.lift J
    ((Ideal.Quotient.mk _).comp (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R))))
    (by
      intro x hx
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact deltaDivisionTorsionMap_ideal_le_span D d J hx)

/-- R/Jからの標準射はRの代表元上で、二段階商への射とmod d商射の合成に一致する。 -/
@[simp] theorem deltaDivisionQuotientMap_mk (D : DeltaStructure p R) (d : R)
    (J : Ideal R) (x : R) :
    deltaDivisionQuotientMap D d J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (deltaDivisionTorsionMap D d (fun x : J ↦ (x : R)) x) := rfl

end SerrePositivity.BhattScholze
