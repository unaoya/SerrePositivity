module

public import SerrePositivity.BhattScholze.Andre.Remark715.PowerRootMonicCompletedInput

/-!
# André A1-a：完備入力環からの環射の外延性

## 概要

原典の順序の完備入力環から p 完備環への環射は、係数と全根の像で決まる。
BS Rem 7.15（著者版 p.62）の入力作用を含む比較。

## 方針

主商射、p 完備化、無限根多項式環の三つの外延性を順に適用する。
原典を補う明示的な係数・根による経路。

## 規約

この外延性にはモニック性は不要。標的の通常の p 完備性を要求する。

## 使われ方

全根の保存から、完備入力環全体での可換性を結論する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.Andre
variable {R : Type u} [CommRing R] (p : ℕ) (hp : 0 < p) (f : Polynomial R)
variable {B : Type v} [CommRing B] [IsAdicComplete (Ideal.span {(p : B)}) B]
local notation "P" => PowerRootPolynomial R p hp
local notation "CP" => AdicCompletion (Ideal.span {(p : P)}) P
local notation "z" => powerRootPolynomialBaseMap R p hp f
local notation "SI" => PowerRootMonicCompletedInput p hp f
local notation "lS" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {algebraMap P CP z})) (algebraMap P CP)

/-- 概要：p 完備な標的への完備入力射は係数と全根の像で決まる。
方針：主商と完備化の外延性を通じて無限根多項式環の外延性へ帰着する。
規約：源のモニック性・標的の p 正則性は要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の全入力作用の保存。 -/
theorem powerRootMonicCompletedInput_ringHom_ext (F G : SI →+* B)
    (hc : (F.comp lS).comp (algebraMap R P) = (G.comp lS).comp (algebraMap R P))
    (hr : ∀ n, F (lS (powerRootPolynomialVariable R p hp n)) =
      G (lS (powerRootPolynomialVariable R p hp n))) : F = G := by
  apply Ideal.Quotient.ringHom_ext
  apply primeAdicCompletion_ringHom_ext P p
  exact powerRootPolynomial_ringHom_ext p hp _ _ hc hr

end SerrePositivity.BhattScholze.Andre
