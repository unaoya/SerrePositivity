module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# イデアルによる almost zero 加群

`I` が加群全体を消すことを almost zero と定義する。
部分加群・商・同型で保たれ、完全列の両端を `I` が消せば中央は `I²` で消える。
従って `I²=I` の場合には拡大で閉じる。perfectoid 性、derived 完備性、
長さや CLMST の引用には依存しない、一般の加群の命題である。
-/

@[expose] public section

universe u v w z

namespace SerrePositivity.Almost

variable {R : Type u} [CommRing R]

/-- イデアル `I` の全ての元が加群 `M` 全体を消すこと。 -/
def IsAlmostZero (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  I ≤ Module.annihilator R M

namespace IsAlmostZero

variable {I J : Ideal R} {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- almost zero の条件を、元の作用が零であるという形に書き換える。 -/
theorem iff_smul_eq_zero : IsAlmostZero I M ↔ ∀ a ∈ I, ∀ m : M, a • m = 0 := by
  simp only [IsAlmostZero, IsConcreteLE.le_iff, Module.mem_annihilator]

/-- almost zero 加群上では、イデアルの元の作用は零。 -/
theorem smul_eq_zero (hM : IsAlmostZero I M) {a : R} (ha : a ∈ I) (m : M) : a • m = 0 :=
  Module.mem_annihilator.mp (hM ha) m

/-- 零加群は任意のイデアルに関して almost zero。 -/
theorem of_subsingleton (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    [Subsingleton M] : IsAlmostZero I M := by
  apply iff_smul_eq_zero.mpr
  intro a _ m
  exact Subsingleton.elim _ _

/-- 零イデアルに関しては全ての加群が almost zero。 -/
theorem bot (M : Type v) [AddCommGroup M] [Module R M] :
    IsAlmostZero (⊥ : Ideal R) M := bot_le

/-- より小さいイデアルへは almost zero の条件を制限できる。 -/
theorem of_le (hIJ : I ≤ J) (hM : IsAlmostZero J M) : IsAlmostZero I M := hIJ.trans hM

/-- almost zero 加群へ単射で入る加群も almost zero。 -/
theorem of_injective (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hN : IsAlmostZero I N) : IsAlmostZero I M :=
  hN.trans (f.annihilator_le_of_injective hf)

/-- almost zero 加群の全射像も almost zero。 -/
theorem of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hM : IsAlmostZero I M) : IsAlmostZero I N :=
  hM.trans (f.annihilator_le_of_surjective hf)

/-- almost zero の条件は線形同型で保たれる。 -/
theorem of_equiv (e : M ≃ₗ[R] N) (hM : IsAlmostZero I M) : IsAlmostZero I N :=
  of_surjective e.toLinearMap e.surjective hM

/-- 線形同型な加群は同じ almost zero 条件を満たす。 -/
theorem equiv_iff (e : M ≃ₗ[R] N) : IsAlmostZero I M ↔ IsAlmostZero I N :=
  ⟨of_equiv e, of_equiv e.symm⟩

/-- almost zero 加群の部分加群も almost zero。 -/
theorem submodule (hM : IsAlmostZero I M) (S : Submodule R M) : IsAlmostZero I S :=
  of_injective S.subtype S.subtype_injective hM

/-- almost zero 加群の商も almost zero。 -/
theorem quotient (hM : IsAlmostZero I M) (S : Submodule R M) : IsAlmostZero I (M ⧸ S) :=
  of_surjective S.mkQ S.mkQ_surjective hM

/-- 完全列の両端を `I` が消すなら、中央を `I²` が消す。
射の単射性・全射性は、この中央での完全性からの結論には不要。 -/
theorem of_exact_mul {L : Type z} [AddCommGroup L] [Module R L]
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hfg : Function.Exact f g)
    (hL : IsAlmostZero I L) (hN : IsAlmostZero I N) : IsAlmostZero (I * I) M := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro m
  have hg : g (b • m) = 0 := by rw [g.map_smul, hN.smul_eq_zero hb]
  obtain ⟨l, hl⟩ := (hfg (b • m)).mp hg
  rw [mul_smul, ← hl, ← f.map_smul, hL.smul_eq_zero ha, f.map_zero]

/-- `I²=I` のとき almost zero 加群は完全列での拡大で閉じる。 -/
theorem of_exact {L : Type z} [AddCommGroup L] [Module R L]
    (hI : I * I = I) (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hfg : Function.Exact f g)
    (hL : IsAlmostZero I L) (hN : IsAlmostZero I N) : IsAlmostZero I M := by
  simpa only [hI] using of_exact_mul f g hfg hL hN

end IsAlmostZero

end SerrePositivity.Almost
