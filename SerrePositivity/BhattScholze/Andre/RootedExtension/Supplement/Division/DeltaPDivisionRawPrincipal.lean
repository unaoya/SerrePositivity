module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionFactorialEquiv
public import SerrePositivity.BhattScholze.Delta.DividedPower.PrincipalDPFactorialEquiv

/-! # 正則raw δ p除算包と分冪表示環の実A代数同型

既存の中間仮定を明示して通常環を比較する。導来pushout比較は含めない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (hA : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : A))
variable (hpA : Function.Injective (fun a : A ↦ (p : A) * a))
variable (D : DeltaStructure p A) (y : A)
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "S₀" => pDivisionFactorialSubring p (fun _ : Unit ↦ y)

omit [Fact p.Prime] in
/-- 定数の一元入力では、階乗部分環は単一添字の宇宙レベルに依存しない。 -/
theorem deltaPDivisionUnaryFactorialSubring_eq :
    pDivisionFactorialSubring p (fun _ : σ ↦ y) =
      pDivisionFactorialSubring p (fun _ : Unit ↦ y) := by
  have hr : Set.range (fun z : σ × ℕ ↦
      pDivisionFactorialValue p (fun _ : σ ↦ y) z.1 z.2) =
      Set.range (fun z : Unit × ℕ ↦
        pDivisionFactorialValue p (fun _ : Unit ↦ y) z.1 z.2) := by
    ext z
    constructor
    · rintro ⟨⟨s, n⟩, rfl⟩
      exact ⟨((), n), rfl⟩
    · rintro ⟨⟨s, n⟩, rfl⟩
      exact ⟨((default : σ), n), rfl⟩
  unfold pDivisionFactorialSubring
  rw [hr]

/-- 同じ具体的階乗部分環を通る、raw δ p除算包と分冪表示環の標準環同型。 -/
def deltaPDivisionRawPrincipalEquiv : B₀ ≃+* PrincipalDPPresentation A y :=
  ((deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA).trans
    (RingEquiv.subringCongr (deltaPDivisionUnaryFactorialSubring_eq (p := p) (σ := σ) y))).trans
      (principalDPFactorialEquiv hA hpA D y hy).symm

/-- 標準環同型は、元のAからの全基底係数の像を保つ。 -/
theorem deltaPDivisionRawPrincipalEquiv_coeff (a : A) :
    deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy (j₀ a) =
      algebraMap A (PrincipalDPPresentation A y) a := by
  have hb : deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA (j₀ a) =
      pDivisionFactorialBase p (fun _ : σ ↦ y) a := by
    apply Subtype.ext
    exact deltaPDivisionRawFactorialEquiv_coeff (σ := σ) D y hpA hg v hv hy hA a
  rw [deltaPDivisionRawPrincipalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, hb]
  change (principalDPFactorialEquiv hA hpA D y hy).symm
    (pDivisionFactorialBase p (fun _ : Unit ↦ y) a) = _
  rw [← principalDPFactorialEquiv_coeff hA hpA D y hy a, RingEquiv.symm_apply_apply]

/-- 元の自然なA作用を保つ、raw δ p除算包と分冪表示環のA代数同型。 -/
def deltaPDivisionRawPrincipalAlgEquiv : B₀ ≃ₐ[A] PrincipalDPPresentation A y :=
  { deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy with
    commutes' := fun a ↦ deltaPDivisionRawPrincipalEquiv_coeff hA hpA D y hg v hv hy a }

/-- 全raw階乗生成元は、対応する表示環の標準分冪生成元へ写る。 -/
theorem deltaPDivisionRawPrincipalEquiv_factorial (n : ℕ) :
    deltaPDivisionRawPrincipalEquiv hA hpA D y hg v hv hy
      (deltaPDivisionRawFactorialQuotient D (fun _ : σ ↦ y) hA (default : σ) n) =
        principalDPGenerator y n := by
  have hb : deltaPDivisionRawFactorialEquiv (σ := σ) D y hpA hg v hv hy hA
      (deltaPDivisionRawFactorialQuotient D (fun _ : σ ↦ y) hA (default : σ) n) =
      (⟨pDivisionFactorialValue p (fun _ : σ ↦ y) (default : σ) n,
        pDivisionFactorialSubring_value_mem (fun _ : σ ↦ y) (default : σ) n⟩ :
        pDivisionFactorialSubring p (fun _ : σ ↦ y)) := by
    apply Subtype.ext
    exact deltaPDivisionRawFactorialEquiv_factorial (σ := σ) D y hpA hg v hv hy hA (default : σ) n
  rw [deltaPDivisionRawPrincipalEquiv, RingEquiv.trans_apply, RingEquiv.trans_apply, hb]
  change (principalDPFactorialEquiv hA hpA D y hy).symm
    (⟨pDivisionFactorialValue p (fun _ : Unit ↦ y) () n,
      pDivisionFactorialSubring_value_mem (fun _ : Unit ↦ y) () n⟩ : S₀) = _
  rw [← principalDPFactorialEquiv_generator hA hpA D y hy n, RingEquiv.symm_apply_apply]

end SerrePositivity.BhattScholze
