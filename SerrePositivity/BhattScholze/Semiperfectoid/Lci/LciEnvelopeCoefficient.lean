module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Flat.Basic

/-!
# 自由変数包絡の係数商

## 概要
自由 δ 環を基底生成元と初期変数で割ると、残りの δ 座標の多項式環となる。

## 方針
高い座標の番号を一つずらし、二つの環射が互いに逆であることを生成元上で確かめる。

## 規約
BS 著者版 Example 7.9 の未完備な係数商。商に δ 構造は要求しない。

## 使われ方
初期変数を切り離した後の p の正則性と剰余の底変換。
-/

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace SerrePositivity.BhattScholze

variable {A : Type u} [CommRing A] {S : Type v}

/-- 概要：初期変数と基底の d を零にすると、残る変数は d 剰余上で自由。
方針：初期変数は零、後続変数は添字を一つ下げて評価し、後続変数を戻す写像を作る。
規約：BS 著者版 Example 7.9 の自由変数模型。通常の商環を用いる。
使われ方：普遍自由変数の d 剰余で、初期関係の Koszul 分解を分離する。 -/
theorem Semiperfectoid.exists_freeDelta_initialQuotient_equiv (d : A) :
    let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
    let I : Ideal A := Ideal.span {d}
    let J : Ideal U := Ideal.span {MvPolynomial.C d} ⊔
      Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
    ∃ e : (U ⧸ J) ≃+* MvPolynomial (S × ℕ) (A ⧸ I),
      (∀ a, e (Ideal.Quotient.mk J (MvPolynomial.C a)) =
        MvPolynomial.C (Ideal.Quotient.mk I a)) ∧
      ∀ s n, e (Ideal.Quotient.mk J (MvPolynomial.X (s, n + 1))) = MvPolynomial.X (s, n) := by
  let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
  let I : Ideal A := Ideal.span {d}
  let J : Ideal U := Ideal.span {MvPolynomial.C d} ⊔
    Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
  let V := MvPolynomial (S × ℕ) (A ⧸ I)
  let q := Ideal.Quotient.mk J
  let q₀ := Ideal.Quotient.mk I
  let C : A →+* U := MvPolynomial.C
  let C₀ : (A ⧸ I) →+* V := MvPolynomial.C
  let f : U →+* V := MvPolynomial.eval₂Hom (C₀.comp q₀) fun
    | (_, 0) => 0
    | (s, n + 1) => MvPolynomial.X (s, n)
  have hfC (a : A) : f (C a) = C₀ (q₀ a) := MvPolynomial.eval₂Hom_C ..
  have hf0 (s : S) : f (MvPolynomial.X (s, 0)) = 0 := MvPolynomial.eval₂Hom_X' ..
  have hfX (s : S) (n : ℕ) : f (MvPolynomial.X (s, n + 1)) = MvPolynomial.X (s, n) :=
    MvPolynomial.eval₂Hom_X' ..
  have hJ : J ≤ RingHom.ker f := by
    apply sup_le
    · apply (RingHom.ker f).span_singleton_le_iff_mem.mpr
      change f (C d) = 0
      rw [hfC, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton d)),
        map_zero]
    · apply Ideal.span_le.mpr
      rintro _ ⟨s, rfl⟩
      exact hf0 s
  let fQ : U ⧸ J →+* V := Ideal.Quotient.lift J f hJ
  have hc : I ≤ RingHom.ker (q.comp C) := by
    apply (RingHom.ker (q.comp C)).span_singleton_le_iff_mem.mpr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (show Ideal.span {C d} ≤ J from le_sup_left)
      (Ideal.subset_span (Set.mem_singleton (C d)))
  let c : A ⧸ I →+* U ⧸ J := Ideal.Quotient.lift I (q.comp C) hc
  let g : V →+* U ⧸ J := MvPolynomial.eval₂Hom c fun z =>
    q (MvPolynomial.X (z.1, z.2 + 1))
  have hgC (a : A ⧸ I) : g (C₀ a) = c a := MvPolynomial.eval₂Hom_C ..
  have hgX (s : S) (n : ℕ) : g (MvPolynomial.X (s, n)) = q (MvPolynomial.X (s, n + 1)) :=
    MvPolynomial.eval₂Hom_X' ..
  have hfg : fQ.comp g = RingHom.id V := by
    apply MvPolynomial.ringHom_ext
    · intro a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      change fQ (g (C₀ (q₀ b))) = C₀ (q₀ b)
      rw [hgC]
      exact hfC b
    · rintro ⟨s, n⟩
      change fQ (g (MvPolynomial.X (s, n))) = MvPolynomial.X (s, n)
      rw [hgX]
      exact hfX s n
  have hgf : g.comp fQ = RingHom.id (U ⧸ J) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change g (f (C a)) = q (C a)
      rw [hfC, hgC]
      rfl
    · rintro ⟨s, _ | n⟩
      · change g (f (MvPolynomial.X (s, 0))) = q (MvPolynomial.X (s, 0))
        rw [hf0, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.mpr
          ((show Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0)) ≤ J from le_sup_right)
            (Ideal.subset_span (Set.mem_range_self s)))).symm
      · change g (f (MvPolynomial.X (s, n + 1))) = q (MvPolynomial.X (s, n + 1))
        rw [hfX, hgX]
  have hl : Function.LeftInverse g fQ := RingHom.congr_fun hgf
  have hr : Function.RightInverse g fQ := RingHom.congr_fun hfg
  exact ⟨RingEquiv.ofBijective fQ ⟨hl.injective, hr.surjective⟩, hfC, hfX⟩

/-- 概要：係数の d 剰余での正則性は、自由変数模型の初期関係の商に移る。
方針：後続座標の多項式環の自由性と、構成した商同型を使う。
規約：BS 著者版 Example 7.9 の普遍係数商。
使われ方：普遍向き付き prism の p 正則性を初期関係の商へ運ぶ。 -/
theorem Semiperfectoid.freeDelta_initialQuotient_scalar_regular (d a : A)
    (ha : IsSMulRegular (A ⧸ Ideal.span {d}) (Ideal.Quotient.mk (Ideal.span {d}) a)) :
    let U := _root_.SerrePositivity.BhattScholze.RelativeFreeDeltaRing (R := A) S
    let J : Ideal U := Ideal.span {MvPolynomial.C d} ⊔
      Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))
    IsRegular (Ideal.Quotient.mk J (MvPolynomial.C a)) := by
  obtain ⟨e, hC, _⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_freeDelta_initialQuotient_equiv (S := S) d
  let V := MvPolynomial (S × ℕ) (A ⧸ Ideal.span {d})
  have hV : IsSMulRegular V (MvPolynomial.C (Ideal.Quotient.mk (Ideal.span {d}) a)) :=
    ha.of_flat (S := V)
  have hl : IsLeftRegular (Ideal.Quotient.mk
      (Ideal.span {MvPolynomial.C d} ⊔
        Ideal.span (Set.range fun s : S => MvPolynomial.X (s, 0))) (MvPolynomial.C a)) := by
    intro x y hxy
    apply e.injective
    apply hV
    have hh := congrArg e hxy
    simpa only [map_mul, hC, smul_eq_mul] using hh
  exact ⟨hl, fun x y hxy => hl (by simpa only [mul_comm] using hxy)⟩

end SerrePositivity.BhattScholze
