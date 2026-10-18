module

public import SerrePositivity.KST.DerivedBlowup.ExteriorFiniteness
public import SerrePositivity.KST.DerivedBlowup.ExteriorDegreeZero
public import SerrePositivity.KST.DerivedBlowup.ChartComplexes

/-!
概要：KST Def3.1 の有限列の外積 Koszul 複体と空列での模型比較。
方針：有限自由加群上の線形結合を微分に取り、有限性と次数境界を具体化する。
規約：反復 cone Koszul 複体への一般の比較はまだ含まない。
使われ方：既存 koszulComplex と外積模型の比較の帰納法。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {n : ℕ}

/-- 概要：有限列に対応する整数次数の外積 Koszul 複体。
方針：自由生成元の線形結合を収縮微分にする。
規約：KST Def3.1、生成元の次数は−1。使われ方：反復 cone 模型の比較対象。 -/
abbrev sequenceExteriorCochain (x : Fin n → R) :=
  exteriorKoszulCochain (Finsupp.linearCombination R x)

/-- 概要：有限列の外積 Koszul 複体の各項は有限生成。
方針：有限自由生成加群に一般の外積有限性を適用する。
規約：KST Def3.1。使われ方：チャートの完全複体性。 -/
theorem sequenceExteriorCochain_finite (x : Fin n → R) (q : ℤ) :
    Module.Finite R ((sequenceExteriorCochain x).X q) :=
  exteriorKoszulCochain_finite _ q

/-- 概要：有限列の外積 Koszul 複体の各項は自由。
方針：有限自由生成加群の同次外積の基底を使う。
規約：KST Def3.1。使われ方：チャートの項の射影性。 -/
theorem sequenceExteriorCochain_free (x : Fin n → R) (q : ℤ) :
    Module.Free R ((sequenceExteriorCochain x).X q) :=
  exteriorKoszulCochain_free _ q

/-- 概要：長さnの外積 Koszul 複体は−n未満で零。
方針：標準基底の個数を一般の生成系の次数境界に代入する。
規約：KST Def3.1。使われ方：反復 cone 模型との有限振幅比較。 -/
theorem sequenceExteriorCochain_isZero_X_lt (x : Fin n → R)
    (q : ℤ) (hq : q < -(n : ℤ)) : IsZero ((sequenceExteriorCochain x).X q) := by
  let b : Module.Basis (Fin n) R (Fin n →₀ R) := Finsupp.basisSingleOne
  exact exteriorKoszulCochain_isZero_X_lt (R := R) (M := Fin n →₀ R) (I := Fin n)
    b b.span_eq (Finsupp.linearCombination R x) q (by simpa only [Nat.card_fin] using hq)

/-- 概要：空列の外積 Koszul 複体への単位射は複体同型。
方針：次数0は基底環同型、他次数は両側の零対象性で比較する。
規約：KST Def3.1。使われ方：反復 cone 比較の基底段階。 -/
theorem sequenceExteriorCochain_empty_unit_isIso (x : Fin 0 → R) :
    IsIso (exteriorKoszulUnit (Finsupp.linearCombination R x)) := by
  have : ∀ q, IsIso ((exteriorKoszulUnit (Finsupp.linearCombination R x)).f q) := by
    intro q
    by_cases hq : q = 0
    · subst q
      exact exteriorKoszulUnit_f_zero_isIso _
    · have hs := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
        0 (ModuleCat.of R R) q hq
      have ht : IsZero ((sequenceExteriorCochain x).X q) := by
        rcases lt_or_gt_of_ne hq with hneg | hpos
        · exact sequenceExteriorCochain_isZero_X_lt x q (by simpa using hneg)
        · exact exteriorKoszulCochain_isZero_X_pos _ q hpos
      exact hs.isIso ht _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 概要：空列では既存の反復 cone Koszul 複体と外積複体が同型。
方針：反復 cone の空列は tensor unit と定義上一致し、単位射が可逆。
規約：KST Def3.1、帰納段階は別工程。使われ方：両 Koszul 模型の比較の出発点。 -/
def sequenceExteriorCochain_empty_iso (x : Fin 0 → R) :
    koszulComplex x ≅ sequenceExteriorCochain x := by
  haveI := sequenceExteriorCochain_empty_unit_isIso x
  exact asIso (exteriorKoszulUnit (Finsupp.linearCombination R x))

end SerrePositivity.KST.DerivedBlowup
