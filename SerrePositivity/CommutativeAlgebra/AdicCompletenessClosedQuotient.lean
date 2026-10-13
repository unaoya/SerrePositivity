module

public import SerrePositivity.CommutativeAlgebra.AdicCompleteness

/-! # 閉じた冪部分加群による、より小さいイデアルへの完備性の移行

I⊆Jについて、J進完備性と各I冪商のJ進分離性からI進完備性を導く。
Noether局所環の極大イデアル進完備性からp進完備性を得る際に使う。
-/

public section
namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- 各I冪商がJ進分離なら、J進完備性は小さいイデアルIへ移る。
Noether性・有限性は冪商の分離性の供給側だけで使う。 -/
theorem isAdicComplete_of_le_of_hausdorff_quotients
    (I J : Ideal R) (hIJ : I ≤ J) [IsAdicComplete J M]
    [∀ n : ℕ, IsHausdorff J (M ⧸ (I ^ n • (⊤ : Submodule R M)))] :
    IsAdicComplete I M := by
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    apply IsHausdorff.haus (inferInstance : IsHausdorff J M) x
    intro n
    exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hIJ n))
  · intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) f (fun {m n} h ↦
      (hf h).mono (Submodule.smul_mono_left (pow_le_pow_left' hIJ m)))
    refine ⟨L, ?_⟩
    intro i
    let Q := I ^ i • (⊤ : Submodule R M)
    have he : Q.mkQ (f i) = Q.mkQ L := by
      apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
      intro n
      let k := max i n
      have hfi : Q.mkQ (f i) = Q.mkQ (f k) := by
        exact (Submodule.Quotient.eq _).mpr (SModEq.sub_mem.mp (hf (le_max_left i n)))
      rw [hfi]
      exact (smodEq_map_pow J Q.mkQ (hL k)).mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (le_max_right i n)))
    exact SModEq.sub_mem.mpr ((Submodule.Quotient.eq _).mp he)

/-- 完備Noether局所環上の有限加群は、極大イデアル以下の任意のイデアルについて完備。
極大イデアル進完備性と各冪商のKrull分離性から導く。 -/
theorem isAdicComplete_finite_of_le_maximalIdeal
    [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Module.Finite R M]
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) : IsAdicComplete I M := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) M :=
    isAdicComplete_finite (R := R) M
  exact isAdicComplete_of_le_of_hausdorff_quotients I (IsLocalRing.maximalIdeal R) hI

end SerrePositivity
