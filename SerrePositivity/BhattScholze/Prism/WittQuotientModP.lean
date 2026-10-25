module

public import SerrePositivity.BhattScholze.Prism.WittDistinguishedQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Witt商のmod pと係数環の商

任意のWitt元dについて(W(k)/(d))/(p)≃k/(d₀)を構成する。
標準商射上の式を明示し、distinguished性や完備性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]

/-- Witt商のmod pを、第0係数による係数環の商に同定する。 -/
def wittQuotientModPEquiv (d : WittVector p k) :
    ((WittVector p k ⧸ Ideal.span {d}) ⧸ Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})}) ≃+*
      k ⧸ Ideal.span {d.coeff 0} := by
  let I : Ideal (WittVector p k) := Ideal.span {d}
  let P : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k)}
  have hP : P.map (Ideal.Quotient.mk I) = Ideal.span {(p : WittVector p k ⧸ I)} := by
    simp [P, Ideal.map_span]
  let e := WittVector.quotientPEquiv (p := p) (k := k)
  have hI : Ideal.span {d.coeff 0} = (I.map (Ideal.Quotient.mk P)).map e.toRingHom := by
    simp only [I, Ideal.map_span, Set.image_singleton]
    change Ideal.span {d.coeff 0} =
      Ideal.span {(WittVector.quotientPEquiv (p := p) (k := k)
        (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k)}) d))}
    rfl
  exact ((Ideal.quotEquivOfEq hP.symm).trans (DoubleQuot.quotQuotEquivComm I P)).trans
    (Ideal.quotientEquiv _ _ e hI)

/-- 同型はWitt代表元の第0係数を取る。 -/
@[simp] theorem wittQuotientModPEquiv_mk (d x : WittVector p k) :
    wittQuotientModPEquiv p k d
      (Ideal.Quotient.mk (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
        (Ideal.Quotient.mk (Ideal.span {d}) x)) =
      Ideal.Quotient.mk (Ideal.span {d.coeff 0}) (x.coeff 0) := by
  rfl

end SerrePositivity.BhattScholze
