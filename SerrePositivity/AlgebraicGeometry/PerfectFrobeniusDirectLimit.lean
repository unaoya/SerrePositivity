module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.Algebra.Group.Commute.Basic

/-!
概要：完全な環の同じFrobenius順極限を、元の環へ自然な同型で戻す。
方針：元のp乗環準同型の逆の冪を有限段で使い、順極限の普遍性で同型を作る。
規約：pの像が零という仮定を保持し、零環を除外しない。
使われ方：BS17 Theorem 4.1(i)の指定されたaffine構造層版の元のconerve（H01）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01a）。 -/
def perfectFrobeniusStageMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) : A →+* A :=
  ((RingEquiv.ofBijective (projectivePrimePowerRingHom (A := A) p hp hA) hFA).symm.toRingHom) ^ n

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01b）。 -/
theorem perfectFrobeniusStageMap_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    perfectFrobeniusStageMap A p hp hA hFA 0 = RingHom.id A := by
  rfl

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01c）。 -/
theorem perfectFrobeniusStageMap_succ_comp (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) :
    (perfectFrobeniusStageMap A p hp hA hFA (n+1)).comp
      (projectivePrimePowerRingHom (A := A) p hp hA) =
        perfectFrobeniusStageMap A p hp hA hFA n := by
  let e := RingEquiv.ofBijective (projectivePrimePowerRingHom (A := A) p hp hA) hFA
  have he : e.symm.toRingHom * e.toRingHom = 1 := by
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  change (e.symm.toRingHom ^ (n+1)) * e.toRingHom = e.symm.toRingHom ^ n
  rw [pow_succ, mul_assoc, he, mul_one]

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01d）。 -/
def perfectFrobeniusLimitMap (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    FrobeniusDirectLimit A p hp hA →+* A := by
  let φ := projectivePrimePowerRingHom (A := A) p hp hA
  let e := RingEquiv.ofBijective φ hFA
  let ψ := e.symm.toRingHom
  have h₁ : ψ * φ = 1 := by
    apply RingHom.ext
    intro x
    exact e.symm_apply_apply x
  have h₂ : φ * ψ = 1 := by
    apply RingHom.ext
    intro x
    exact e.apply_symm_apply x
  have hc : Commute ψ φ := h₁.trans h₂.symm
  refine DirectLimit.Ring.lift (fun _ : ℕ ↦ A)
    (frobeniusDirectSystemMap A p hp hA) A
    (perfectFrobeniusStageMap A p hp hA hFA) ?_
  intro i j hij x
  change (ψ ^ j) ((φ ^ (j-i)) x) = (ψ ^ i) x
  have he : ψ ^ j * φ ^ (j-i) = ψ ^ i := by
    calc
      ψ ^ j * φ ^ (j-i) = (ψ ^ i * ψ ^ (j-i)) * φ ^ (j-i) := by
        rw [← pow_add, Nat.add_sub_of_le hij]
      _ = ψ ^ i * (ψ ^ (j-i) * φ ^ (j-i)) := mul_assoc _ _ _
      _ = ψ ^ i := by rw [← hc.mul_pow, h₁, one_pow, mul_one]
  exact congrArg (fun z : A →+* A ↦ z x) he

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01e）。 -/
theorem perfectFrobeniusLimitMap_comp_of (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) (n : ℕ) :
    (perfectFrobeniusLimitMap A p hp hA hFA).comp
      (frobeniusDirectLimitOf A p hp hA n) = perfectFrobeniusStageMap A p hp hA hFA n := by
  rfl

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01f）。 -/
def perfectFrobeniusLimitEquiv (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    FrobeniusDirectLimit A p hp hA ≃+* A := by
  let F := perfectFrobeniusLimitMap A p hp hA hFA
  let I := frobeniusDirectLimitOf A p hp hA 0
  have h₁ : F.comp I = RingHom.id A := by
    exact (perfectFrobeniusLimitMap_comp_of A p hp hA hFA 0).trans
      (perfectFrobeniusStageMap_zero A p hp hA hFA)
  have h₂ : I.comp F = RingHom.id (FrobeniusDirectLimit A p hp hA) := by
    apply DirectLimit.Ring.hom_ext
    intro n
    change I.comp ((perfectFrobeniusLimitMap A p hp hA hFA).comp
      (frobeniusDirectLimitOf A p hp hA n)) =
        (RingHom.id (FrobeniusDirectLimit A p hp hA)).comp
          (frobeniusDirectLimitOf A p hp hA n)
    rw [perfectFrobeniusLimitMap_comp_of, RingHom.id_comp]
    apply RingHom.ext
    intro x
    apply (frobeniusDirectLimitOf_eq_iff A p hp hA 0 n _ x).mpr
    refine ⟨n, Nat.zero_le n, le_rfl, ?_⟩
    let φ := projectivePrimePowerRingHom (A := A) p hp hA
    let e := RingEquiv.ofBijective φ hFA
    let ψ := e.symm.toRingHom
    have hl : φ * ψ = 1 := by
      apply RingHom.ext
      intro x
      exact e.apply_symm_apply x
    have hr : ψ * φ = 1 := by
      apply RingHom.ext
      intro x
      exact e.symm_apply_apply x
    have hc : Commute φ ψ := hl.trans hr.symm
    simp only [frobeniusDirectSystemMap, Nat.sub_zero, Nat.sub_self, pow_zero]
    change (φ ^ n * ψ ^ n) x = x
    rw [← hc.mul_pow, hl, one_pow]
    rfl
  exact RingEquiv.ofRingHom F I h₁ h₂

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01g）。 -/
theorem perfectFrobeniusLimitEquiv_comp_of_zero (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA)) :
    (perfectFrobeniusLimitEquiv A p hp hA hFA).toRingHom.comp
      (frobeniusDirectLimitOf A p hp hA 0) = RingHom.id A := by
  change (perfectFrobeniusLimitMap A p hp hA hFA).comp
    (frobeniusDirectLimitOf A p hp hA 0) = RingHom.id A
  exact (perfectFrobeniusLimitMap_comp_of A p hp hA hFA 0).trans
    (perfectFrobeniusStageMap_zero A p hp hA hFA)

/-- 同じp乗の逆と有限段の射を保持する比較（計画H01h）。 -/
theorem perfectFrobeniusLimitEquiv_naturality {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) (hB : (p : B) = 0)
    (hFA : Function.Bijective (projectivePrimePowerRingHom (A := A) p hp hA))
    (hFB : Function.Bijective (projectivePrimePowerRingHom (A := B) p hp hB)) :
    (perfectFrobeniusLimitEquiv B p hp hB hFB).toRingHom.comp
      (frobeniusDirectLimitMap p hp hA hB f) =
    f.comp (perfectFrobeniusLimitEquiv A p hp hA hFA).toRingHom := by
  let eA := perfectFrobeniusLimitEquiv A p hp hA hFA
  let eB := perfectFrobeniusLimitEquiv B p hp hB hFB
  have hs : Function.Surjective (frobeniusDirectLimitOf A p hp hA 0) := eA.symm.surjective
  have ha (x : A) : eA (frobeniusDirectLimitOf A p hp hA 0 x) = x :=
    RingHom.congr_fun (perfectFrobeniusLimitEquiv_comp_of_zero A p hp hA hFA) x
  have hb (x : B) : eB (frobeniusDirectLimitOf B p hp hB 0 x) = x :=
    RingHom.congr_fun (perfectFrobeniusLimitEquiv_comp_of_zero B p hp hB hFB) x
  apply RingHom.ext
  intro z
  obtain ⟨x, rfl⟩ := hs z
  change eB (frobeniusDirectLimitMap p hp hA hB f
    (frobeniusDirectLimitOf A p hp hA 0 x)) = f (eA (frobeniusDirectLimitOf A p hp hA 0 x))
  rw [frobeniusDirectLimitMap_of, ha, hb]

end SerrePositivity.AlgebraicGeometry
