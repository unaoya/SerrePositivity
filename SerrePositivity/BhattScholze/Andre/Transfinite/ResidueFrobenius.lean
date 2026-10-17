module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import Mathlib.Algebra.Colimit.Ring
/-! # 有向余極限の mod p Frobenius

BS Thm 7.14（著者版 p.61）の極限段に必要な、剰余 Frobenius 全射性の保存。
Fontaine 核の単項性や完備化による保存とは区別する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.BhattScholze.Andre.Transfinite
universe u
variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    (p : ℕ) [Fact p.Prime]
omit [Fact p.Prime] in
/-- ## 概要
各段で mod p の p 乗写像が全射なら、有向余極限でも全射である。
BS Thm 7.14（著者版 p.61）の極限段で perfectoid の一条件を保存する。

## 方針
余極限の元を一段に降ろし、その段で根を選ぶ。誤差の p 倍表示を環準同型で移送する。

## 規約
p ねじれと零環を許す。完備性や遷移写像の単射性は仮定しない。

## 使われ方
超限反復における極限段の剰余 Frobenius 条件の検証に使う。
-/
theorem directLimit_mod_p_pow_surjective (hF : ∀ i, Function.Surjective
    (fun x : R i ⧸ Ideal.span {(p : R i)} ↦ x ^ p)) :
    Function.Surjective (fun x :
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⧸
        Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))} ↦ x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of x
  obtain ⟨y, hy⟩ := hF i (Ideal.Quotient.mk _ x)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hd : y ^ p - x ∈ Ideal.span {(p : R i)} :=
    Ideal.Quotient.eq.mp (by simpa only [map_pow] using hy)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hd
  refine ⟨Ideal.Quotient.mk _ (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i y), ?_⟩
  dsimp only
  rw [← map_pow]
  apply Ideal.Quotient.eq.mpr
  rw [← map_pow, ← map_sub]
  apply Ideal.mem_span_singleton.mpr
  refine ⟨Ring.DirectLimit.of R (fun i j h ↦ f i j h) i a, ?_⟩
  rw [ha, map_mul, map_natCast]

/-- ## 概要
perfectoid 環の有向余極限では mod p Frobenius が全射である。
BS Thm 7.14（著者版 p.61）の極限段の一条件。

## 方針
非零の場合は perfectoid の定義から全射性を取り出し、零環の場合は自明な根を選ぶ。

## 規約
余極限そのものの perfectoid 性や p 進完備性は結論しない。

## 使われ方
perfectoid 塔の極限段で、完備性と Fontaine 核を別途検証するときに使う。
-/
theorem directLimit_mod_p_pow_surjective_of_perfectoid
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    Function.Surjective (fun x :
      Ring.DirectLimit R (fun i j h ↦ f i j h) ⧸
        Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))} ↦ x ^ p) := by
  apply directLimit_mod_p_pow_surjective R f p
  intro i
  rcases hR i with hsub | ⟨_, _, _, hF, _⟩
  · let := hsub
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact hF

end SerrePositivity.BhattScholze.Andre.Transfinite
