module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Exact.Basic

/-! # almost zero 加群と almost 同型な線形写像

## 概要

イデアル I が加群全体を消すことを almost zero と定め、部分加群・商・同型で保たれること、完全列の両端を I が消せば中央は I² で消えること（I² = I なら拡大で閉じる）を示す。線形写像の almost 単射・全射・同型を核と余核が I で消えることで定め、合成が I² について同じ条件を満たすことを示す。
BS 著者版 Definition 10.1 では perfectoid 核を指定し、このイデアルによる加群の零化述語を使う。

## 方針

核と余核の零化を完全列で組み合わせる。

## 規約

単一の線形写像の条件と、局所化した圏で二つの対象が同型であることは別の主張で、同一視しない。perfectoid 性・導来完備性・長さ・CLMST の引用には依存しない。

## 使われ方

`CommutativeAlgebra/Almost/Category`・`Almost/Quotient`、LengthAlgebra/Almost、CLMST。
-/

@[expose] public noncomputable section

universe u v w z

section ZeroPart

namespace SerrePositivity.Almost

variable {R : Type u} [CommRing R]

/-- イデアル `I` の全ての元が加群 `M` 全体を消すこと（BS 著者版 Definition 10.1 の完備加群に対する条件を、任意の加群とイデアルに対して表す述語）。 -/
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

end ZeroPart

section MorphismPart

namespace SerrePositivity.Almost

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {L : Type z} [AddCommGroup L] [Module R L]

/-- 線形写像の核が `I` に消されること。 -/
def IsAlmostInjective (I : Ideal R) (f : M →ₗ[R] N) : Prop := IsAlmostZero I f.ker

/-- 線形写像の余核が `I` に消されること。 -/
def IsAlmostSurjective (I : Ideal R) (f : M →ₗ[R] N) : Prop :=
  IsAlmostZero I (N ⧸ f.range)

/-- 個々の線形写像の核と余核がともに `I` に消されること。
局所化した圏での対象の同型関係そのものの定義ではない。 -/
def IsAlmostIso (I : Ideal R) (f : M →ₗ[R] N) : Prop :=
  IsAlmostInjective I f ∧ IsAlmostSurjective I f

namespace IsAlmostInjective

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- almost 単射の条件を、核の元に対する作用として書く。 -/
theorem iff_smul_eq_zero :
    IsAlmostInjective I f ↔ ∀ x : M, f x = 0 → ∀ a ∈ I, a • x = 0 := by
  constructor
  · intro hf x hx a ha
    exact congrArg Subtype.val (hf.smul_eq_zero ha (⟨x, hx⟩ : f.ker))
  · intro hf
    apply IsAlmostZero.iff_smul_eq_zero.mpr
    intro a ha x
    exact Subtype.ext (hf x.1 x.2 a ha)

/-- almost 単射の核を `I` の元は消す。 -/
theorem smul_eq_zero (hf : IsAlmostInjective I f) (x : M) (hx : f x = 0)
    {a : R} (ha : a ∈ I) : a • x = 0 := iff_smul_eq_zero.mp hf x hx a ha

/-- 通常の単射は任意のイデアルに関して almost 単射。 -/
theorem of_injective (f : M →ₗ[R] N) (hf : Function.Injective f) : IsAlmostInjective I f := by
  apply iff_smul_eq_zero.mpr
  intro x hx a _
  have hx0 : x = 0 := hf (hx.trans f.map_zero.symm)
  rw [hx0, smul_zero]

/-- almost 単射の合成の核は `I²` に消される。 -/
theorem comp_mul (hf : IsAlmostInjective I f) (hg : IsAlmostInjective I g) :
    IsAlmostInjective (I * I) (g.comp f) := by
  change I * I ≤ Module.annihilator R (g.comp f).ker
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  apply Subtype.ext
  change (a * b) • (x : M) = 0
  have hx : g (f (x : M)) = 0 := x.2
  have hbf : f (b • (x : M)) = 0 := by
    rw [f.map_smul, hg.smul_eq_zero (f x) hx hb]
  rw [mul_smul, hf.smul_eq_zero _ hbf ha]

/-- `I²=I` なら almost 単射は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostInjective I f) (hg : IsAlmostInjective I g) :
    IsAlmostInjective I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostInjective

namespace IsAlmostSurjective

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- almost 全射とは `I` 倍した任意の元が写像の像に入ること。 -/
theorem iff_smul_mem_range :
    IsAlmostSurjective I f ↔ ∀ a ∈ I, ∀ y : N, a • y ∈ f.range := by
  constructor
  · intro hf a ha y
    have hz := hf.smul_eq_zero ha (Submodule.Quotient.mk y : N ⧸ f.range)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hz
    exact hz
  · intro hf
    apply IsAlmostZero.iff_smul_eq_zero.mpr
    intro a ha y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective f.range y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hf a ha y

/-- almost 全射では、`I` 倍した元は写像の像に入る。 -/
theorem smul_mem_range (hf : IsAlmostSurjective I f) {a : R} (ha : a ∈ I) (y : N) :
    a • y ∈ f.range := iff_smul_mem_range.mp hf a ha y

/-- 通常の全射は任意のイデアルに関して almost 全射。 -/
theorem of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f) : IsAlmostSurjective I f := by
  apply iff_smul_mem_range.mpr
  intro a _ y
  exact hf (a • y)

/-- almost 全射の合成の余核は `I²` に消される。 -/
theorem comp_mul (hf : IsAlmostSurjective I f) (hg : IsAlmostSurjective I g) :
    IsAlmostSurjective (I * I) (g.comp f) := by
  change I * I ≤ Module.annihilator R (L ⧸ (g.comp f).range)
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (g.comp f).range y
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  obtain ⟨n, hn⟩ := hg.smul_mem_range hb y
  obtain ⟨m, hm⟩ := hf.smul_mem_range ha n
  refine ⟨m, ?_⟩
  rw [LinearMap.comp_apply, hm, g.map_smul, hn, mul_smul]

/-- `I²=I` なら almost 全射は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostSurjective I f) (hg : IsAlmostSurjective I g) :
    IsAlmostSurjective I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostSurjective

namespace IsAlmostIso

variable {I : Ideal R} {f : M →ₗ[R] N} {g : N →ₗ[R] L}

/-- 通常の全単射な線形写像は almost 同型条件を満たす。 -/
theorem of_bijective (f : M →ₗ[R] N) (hf : Function.Bijective f) : IsAlmostIso I f :=
  ⟨IsAlmostInjective.of_injective f hf.1, IsAlmostSurjective.of_surjective f hf.2⟩

/-- 恒等写像は任意のイデアルに関して almost 同型条件を満たす。 -/
theorem refl (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsAlmostIso I (LinearMap.id (R := R) (M := M)) :=
  of_bijective _ Function.bijective_id

/-- 線形同型は、核と余核による almost 同型条件を満たす。 -/
theorem of_equiv (e : M ≃ₗ[R] N) : IsAlmostIso I e.toLinearMap := of_bijective _ e.bijective

/-- 二つの almost 同型写像の合成は `I²` に関して almost 同型条件を満たす。 -/
theorem comp_mul (hf : IsAlmostIso I f) (hg : IsAlmostIso I g) :
    IsAlmostIso (I * I) (g.comp f) :=
  ⟨IsAlmostInjective.comp_mul hf.1 hg.1, IsAlmostSurjective.comp_mul hf.2 hg.2⟩

/-- `I²=I` なら almost 同型写像は合成で閉じる。 -/
theorem comp (hI : I * I = I) (hf : IsAlmostIso I f) (hg : IsAlmostIso I g) :
    IsAlmostIso I (g.comp f) := by simpa only [hI] using comp_mul hf hg

end IsAlmostIso

end SerrePositivity.Almost

end MorphismPart
