module

public import SerrePositivity.CommutativeAlgebra.CompatibleRoot
public import SerrePositivity.HomologicalAlgebra.CompatibleRootQuotientTor
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Completion
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.CommutativeAlgebra.Adic.Complete

/-!
# perfectoid 環の互換 p 冪根で生成されるイデアルと商

## 概要
互換 p 冪根の族が生成するイデアルの平坦性・テンソル・Tor、その商の完全性・tilt・普遍 perfectoid 化・完備化の全射性。

## 方針
共通基盤（CommutativeAlgebra の CompatibleRoot*）の計算を BS の perfectoid 化へつなぐ。

## 規約
—

## 使われ方
CLMST の perfectoid イデアル、BS 著者版 Theorem 7.4 の降下。
-/

universe u

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootIdeal

namespace SerrePositivity.BhattScholze
alias compatibleRootIdeal := SerrePositivity.compatibleRootIdeal
alias span_root_zero_le_compatibleRootIdeal := SerrePositivity.span_root_zero_le_compatibleRootIdeal
alias compatibleRoot_principal_monotone := SerrePositivity.compatibleRoot_principal_monotone
alias mem_compatibleRootIdeal_iff := SerrePositivity.mem_compatibleRootIdeal_iff
alias compatibleRootIdeal_mul_self := SerrePositivity.compatibleRootIdeal_mul_self
alias compatibleRootIdeal_le_ker_of_root_zero := SerrePositivity.compatibleRootIdeal_le_ker_of_root_zero
alias compatibleRootIdeal_map := SerrePositivity.compatibleRootIdeal_map
-- Preserve rewriting through the former computational definitions.
attribute [reducible] compatibleRootIdeal
end SerrePositivity.BhattScholze

end CompatibleRootIdeal

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootIdealFlat

namespace SerrePositivity.BhattScholze
alias compatibleRoot_annihilator_le_succ := SerrePositivity.compatibleRoot_annihilator_le_succ
alias compatibleRoot_transition_kills_kernel := SerrePositivity.compatibleRoot_transition_kills_kernel
alias compatibleRootIdeal_flat := SerrePositivity.compatibleRootIdeal_flat
end SerrePositivity.BhattScholze

end CompatibleRootIdealFlat

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootIdealTensor

namespace SerrePositivity.BhattScholze
alias compatibleRootIdealElement := SerrePositivity.compatibleRootIdealElement
alias compatibleRootIdeal_tensor_singleStage := SerrePositivity.compatibleRootIdeal_tensor_singleStage
alias compatibleRootIdealTensorMap := SerrePositivity.compatibleRootIdealTensorMap
alias compatibleRootIdealTensorMap_tmul := SerrePositivity.compatibleRootIdealTensorMap_tmul
attribute [simp] compatibleRootIdealTensorMap_tmul
alias compatibleRootIdealTensorMap_injective := SerrePositivity.compatibleRootIdealTensorMap_injective
-- Preserve rewriting through the former computational definitions.
attribute [reducible] compatibleRootIdealElement compatibleRootIdealTensorMap
end SerrePositivity.BhattScholze

end CompatibleRootIdealTensor

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootQuotientTor

namespace SerrePositivity.BhattScholze
alias compatibleRootQuotient_tor_subsingleton := SerrePositivity.compatibleRootQuotient_tor_subsingleton
alias compatibleRootQuotient_derivedTensor_concentrated := SerrePositivity.compatibleRootQuotient_derivedTensor_concentrated
end SerrePositivity.BhattScholze

end CompatibleRootQuotientTor

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootPerfectQuotient

namespace SerrePositivity.BhattScholze
alias compatibleRootIdeal_map_frobenius_eq := SerrePositivity.compatibleRootIdeal_map_frobenius_eq
alias compatibleRootQuotient_perfectRing := SerrePositivity.compatibleRootQuotient_perfectRing
end SerrePositivity.BhattScholze

end CompatibleRootPerfectQuotient

/-! ## 両立する根列のtiltへの移送

根列そのものをmod pの逆極限へ送り、untiltの標準図式を証明する。
-/

@[expose] public noncomputable section CompatibleRootTilt

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable [Fact (¬ IsUnit (p : R))]

/-- 根列のn以降をmod pへ送った具体的なtilt元。 -/
def compatibleRootTilt (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    PreTilt R p :=
  ⟨fun m ↦ Ideal.Quotient.mk (Ideal.span {(p : R)}) (ρ (n + m)), by
    intro m
    rw [← map_pow, ← Nat.add_assoc, hρ]⟩

/-- tilt元の全座標は元の根列のmod p像。 -/
@[simp] theorem compatibleRootTilt_coeff
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n m : ℕ) :
    PreTilt.coeff m (compatibleRootTilt ρ hρ n) =
      Ideal.Quotient.mk (Ideal.span {(p : R)}) (ρ (n + m)) := rfl

/-- tilt内でも根列は両立する。 -/
theorem compatibleRootTilt_pow
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    compatibleRootTilt ρ hρ (n + 1) ^ p = compatibleRootTilt ρ hρ n := by
  apply Perfection.ext
  intro m
  change (Ideal.Quotient.mk _ (ρ (n + 1 + m))) ^ p = Ideal.Quotient.mk _ (ρ (n + m))
  rw [← map_pow, show n + 1 + m = n + m + 1 by omega, hρ]

/-- 根列をtiltへ送りuntiltすると、元の根列を復元する。 -/
@[simp] theorem compatibleRootTilt_untilt
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    (compatibleRootTilt ρ hρ n).untilt = ρ n := by
  apply Perfection.teichmullerFun_spec
  intro m
  refine ⟨ρ (n + m), rfl, ?_⟩
  rw [compatibleRoots_pow p ρ hρ n m]

/-- 根をすべて消す射は、tilt上の根イデアルも消す。 -/
theorem compatibleRootTiltIdeal_le_ker
    {T : Type u} [CommRing T] [Fact (¬ IsUnit (p : T))]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (f : R →+* T) (hf : ∀ n, f (ρ n) = 0) :
    compatibleRootIdeal (compatibleRootTilt ρ hρ) ≤
      RingHom.ker (Perfection.map p (modPMap p f)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  apply Perfection.ext
  intro m
  change modPMap p f (Ideal.Quotient.mk _ (ρ (n + m))) = 0
  change Ideal.Quotient.mk _ (f (ρ (n + m))) = 0
  rw [hf, map_zero]

/-- tilt側の根イデアル商は完全。零環の商も含める。 -/
theorem compatibleRootTiltQuotient_perfectRing
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    PerfectRing (PreTilt R p ⧸ compatibleRootIdeal (compatibleRootTilt ρ hρ)) p :=
  compatibleRootQuotient_perfectRing _ (compatibleRootTilt_pow ρ hρ)

end SerrePositivity.BhattScholze

end CompatibleRootTilt

/-! ## 共通層へ移した根・完全係数環のAPIの互換入口

既存のBS宣言名を保ち、証明は共通層の同じ宣言を再利用する。
-/

@[expose] public section CompatibleRootFamilyIdeal

namespace SerrePositivity.BhattScholze
alias compatibleRootFamilyZeroIdeal := SerrePositivity.compatibleRootFamilyZeroIdeal
alias compatibleRootFamilyIdeal := SerrePositivity.compatibleRootFamilyIdeal
alias compatibleRootFamilyZeroIdeal_le := SerrePositivity.compatibleRootFamilyZeroIdeal_le
alias compatibleRootFamilyIdeal_le_ker := SerrePositivity.compatibleRootFamilyIdeal_le_ker
alias compatibleRootFamilyIdeal_mul_self := SerrePositivity.compatibleRootFamilyIdeal_mul_self
alias compatibleRootFamilyIdeal_map_frobenius_eq := SerrePositivity.compatibleRootFamilyIdeal_map_frobenius_eq
alias compatibleRootFamilyQuotient_perfectRing := SerrePositivity.compatibleRootFamilyQuotient_perfectRing
-- Preserve rewriting through the former computational definitions.
attribute [reducible] compatibleRootFamilyZeroIdeal compatibleRootFamilyIdeal
end SerrePositivity.BhattScholze

end CompatibleRootFamilyIdeal

/-! ## 根イデアル商と完備化の制限付き普遍性

BS 著者版 Theorem 7.4の単項・根を持つ場合に向けた部分定理。
試験環の被約性を明示し、候補のperfectoid性と完備化射の全射性は結論しない。
-/

@[expose] public noncomputable section CompatibleRootQuotient

namespace SerrePositivity.BhattScholze
variable {p : ℕ} {R : Type u} [CommRing R]

/-- 最初の元の商から、すべての根の商への標準射。 -/
def compatibleRootQuotientMap (ρ : ℕ → R) :
    R ⧸ Ideal.span {ρ 0} →+* R ⧸ compatibleRootIdeal ρ :=
  Ideal.quotientMap _ (RingHom.id R) (span_root_zero_le_compatibleRootIdeal ρ)

/-- 標準商射の代表元公式。 -/
@[simp] theorem compatibleRootQuotientMap_mk (ρ : ℕ → R) (r : R) :
    compatibleRootQuotientMap ρ (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (compatibleRootIdeal ρ) r := rfl

/-- 完備化前の標準商射は全射。 -/
theorem compatibleRootQuotientMap_surjective (ρ : ℕ → R) :
    Function.Surjective (compatibleRootQuotientMap ρ) :=
  Ideal.quotientMap_surjective Function.surjective_id

/-- 被約環への射は根イデアル商を一意に経由する。 -/
theorem existsUnique_compatibleRootQuotientLift
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] [IsReduced T] (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : R ⧸ compatibleRootIdeal ρ →+* T, l.comp (compatibleRootQuotientMap ρ) = g := by
  let f := g.comp (Ideal.Quotient.mk (Ideal.span {ρ 0}))
  have hK : compatibleRootIdeal ρ ≤ RingHom.ker f :=
    compatibleRootIdeal_le_ker_of_root_zero ρ hρ f (by
      change g (Ideal.Quotient.mk _ (ρ 0)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero])
  let l := Ideal.Quotient.lift (compatibleRootIdeal ρ) f hK
  have hl : l.comp (compatibleRootQuotientMap ρ) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply RingHom.ext
  intro x
  obtain ⟨s, rfl⟩ := compatibleRootQuotientMap_surjective ρ x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hl s).symm

/-- 根イデアル商をp進完備化した具体的候補。 -/
abbrev CompatibleRootCompletion (p : ℕ) (ρ : ℕ → R) :=
  AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootIdeal ρ)})
    (R ⧸ compatibleRootIdeal ρ)

/-- 最初の元の商から、根イデアル商のp進完備化への具体的な射。 -/
def compatibleRootCompletionMap (p : ℕ) (ρ : ℕ → R) :
    R ⧸ Ideal.span {ρ 0} →+* CompatibleRootCompletion p ρ :=
  (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)).comp
    (compatibleRootQuotientMap ρ)

/-- 被約なp進完備環への射は、具体的な完備化候補を一意に経由する。
試験環は一般perfectoid環とは同定せず、被約性と完備性を明示する。 -/
theorem existsUnique_compatibleRootCompletionLift
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] [IsReduced T]
    [IsAdicComplete (Ideal.span {(p : T)}) T] (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : CompatibleRootCompletion p ρ →+* T,
      l.comp (compatibleRootCompletionMap p ρ) = g := by
  obtain ⟨f, hf, hfu⟩ := existsUnique_compatibleRootQuotientLift ρ hρ g
  let l := completionLift (R ⧸ compatibleRootIdeal ρ) T p f
  have hl : l.comp (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)) = f :=
    completionLift_comp _ _ _ f
  refine ⟨l, ?_, ?_⟩
  · change l.comp ((algebraMap _ _).comp (compatibleRootQuotientMap ρ)) = g
    rw [← RingHom.comp_assoc, hl, hf]
  · intro k hk
    apply completionLift_unique _ _ _ f k
    apply hfu
    change (k.comp (algebraMap _ _)).comp (compatibleRootQuotientMap ρ) = g
    rw [RingHom.comp_assoc]
    exact hk

end SerrePositivity.BhattScholze

end CompatibleRootQuotient

/-! ## 根付き商の任意perfectoid試験環への普遍性

既存の根イデアル商の普遍性に、一般perfectoid環の被約性と完備性を供給する。
候補のperfectoid性は別工程の仮定として明示する。Andréの引用は使わない。
-/

@[expose] public noncomputable section CompatibleRootPerfectoidUniversal

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- 根付き商から任意perfectoid環への射は、根イデアル商の完備化を一意に経由する。
零試験環も共通の被約性・完備性の定理で扱う。 -/
theorem existsUnique_compatibleRootCompletionLift_to_perfectoid
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (g : R ⧸ Ideal.span {ρ 0} →+* T) :
    ∃! l : CompatibleRootCompletion p ρ →+* T,
      l.comp (compatibleRootCompletionMap p ρ) = g := by
  let := hT.isReduced T p
  let := hT.isAdicComplete T p
  exact existsUnique_compatibleRootCompletionLift ρ hρ g

/-- 候補のperfectoid性を別途証明すれば、具体的な標準射はperfectoid化である。 -/
theorem compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p) :
    IsPerfectoidization p (compatibleRootCompletionMap p ρ) := by
  refine ⟨hC, ?_⟩
  intro T _ hT g
  exact existsUnique_compatibleRootCompletionLift_to_perfectoid ρ hρ hT g

/-- 根付き商の任意の普遍perfectoid化は、候補のperfectoid性の下で標準候補と同型。 -/
theorem exists_compatibleRootCompletionEquiv_of_isPerfectoidization
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) :
    ∃ e : CompatibleRootCompletion p ρ ≃+* C,
      e.toRingHom.comp (compatibleRootCompletionMap p ρ) = f :=
  let h := compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ hC
  h.exists_equiv p hf

end SerrePositivity.BhattScholze

end CompatibleRootPerfectoidUniversal

/-! ## 根イデアル商のp完備化への標準射の全射性

商の前完備性を既存の全射移送から供給する。
根イデアルの閉性・商の分離性・有限生成性を仮定しない。
-/

@[expose] public noncomputable section CompatibleRootCompletionSurjective

namespace SerrePositivity.BhattScholze
variable {p : ℕ} {R : Type u} [CommRing R]

/-- p前完備な環の根イデアル商は、自身のp作用について前完備。 -/
theorem compatibleRootQuotient_isPrecomplete (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    IsPrecomplete (Ideal.span {(p : R ⧸ compatibleRootIdeal ρ)})
      (R ⧸ compatibleRootIdeal ρ) := by
  let J := compatibleRootIdeal ρ
  let Q := R ⧸ J
  have h : IsPrecomplete (Ideal.span {(p : R)}) Q :=
    isPrecomplete_of_surjective (Ideal.span {(p : R)}) J.mkQ (Submodule.mkQ_surjective J)
  have hh := (IsPrecomplete.map_algebraMap_iff (I := Ideal.span {(p : R)}) (S := Q) (M := Q)).mpr h
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hh

/-- 根イデアル商からそのp完備化への標準射は全射。 -/
theorem compatibleRootCompletion_algebraMap_surjective (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective
      (algebraMap (R ⧸ compatibleRootIdeal ρ) (CompatibleRootCompletion p ρ)) := by
  let := compatibleRootQuotient_isPrecomplete (p := p) ρ
  exact AdicCompletion.of_surjective _ _

/-- 最初の元の商から根イデアル商の完備化への具体的な射は全射。 -/
theorem compatibleRootCompletionMap_surjective (ρ : ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (compatibleRootCompletionMap p ρ) :=
  (compatibleRootCompletion_algebraMap_surjective (p := p) ρ).comp
    (compatibleRootQuotientMap_surjective ρ)

/-- perfectoid基底の根付き商では、候補のperfectoid性があれば任意のperfectoid化は全射。 -/
theorem surjective_of_isPerfectoidization_of_compatibleRoots
    [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hC : IsIntegralPerfectoid (CompatibleRootCompletion p ρ) p)
    {C : Type u} [CommRing C] (f : R ⧸ Ideal.span {ρ 0} →+* C)
    (hf : IsPerfectoidization p f) : Function.Surjective f := by
  let := hR.isAdicComplete R p
  have h := compatibleRootCompletionMap_isPerfectoidization_of_isIntegralPerfectoid ρ hρ hC
  exact (h.surjective_iff p hf).mp (compatibleRootCompletionMap_surjective ρ)

end SerrePositivity.BhattScholze

end CompatibleRootCompletionSurjective

/-! ## 任意根族の商とp完備化の普遍性・標準射

被約なp進完備試験環への普遍性を先に示し、perfectoid試験環への入口を特殊化する。
候補自身のperfectoid性は別の仮定とする。
-/

@[expose] public noncomputable section CompatibleRootFamilyQuotient

namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type u}

/-- 最初の元の全体の商から、全根族の商への標準射。 -/
def compatibleRootFamilyQuotientMap (ρ : σ → ℕ → R) :
    R ⧸ compatibleRootFamilyZeroIdeal ρ →+* R ⧸ compatibleRootFamilyIdeal ρ :=
  Ideal.quotientMap _ (RingHom.id R) (compatibleRootFamilyZeroIdeal_le ρ)

/-- 根族商のp完備化の具体的な環。 -/
abbrev CompatibleRootFamilyCompletion (p : ℕ) (ρ : σ → ℕ → R) :=
  AdicCompletion (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
    (R ⧸ compatibleRootFamilyIdeal ρ)

/-- 最初の元の商から、全根族の商のp完備化への標準射。 -/
def compatibleRootFamilyCompletionMap (p : ℕ) (ρ : σ → ℕ → R) :
    R ⧸ compatibleRootFamilyZeroIdeal ρ →+* CompatibleRootFamilyCompletion p ρ :=
  (algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) _).comp (compatibleRootFamilyQuotientMap ρ)

omit [Fact p.Prime] in
/-- 被約なp進完備試験環への射は、全根族商のp完備化を一意に経由する。
pの素数性、源の完備性、生成族の有限性や非空性は要求しない。 -/
theorem existsUnique_compatibleRootFamilyCompletionLift
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {T : Type u} [CommRing T] [IsReduced T]
    [IsAdicComplete (Ideal.span {(p : T)}) T]
    (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
  let f := g.comp (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ))
  have hf : ∀ s, f (ρ s 0) = 0 := by
    intro s
    change g (Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) (ρ s 0)) = 0
    have hz : Ideal.Quotient.mk (compatibleRootFamilyZeroIdeal ρ) (ρ s 0) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr Ideal.mem_span_range_self
    rw [hz, map_zero]
  have hK := compatibleRootFamilyIdeal_le_ker ρ hρ f hf
  let q := Ideal.Quotient.lift (compatibleRootFamilyIdeal ρ) f hK
  have hq : q.comp (compatibleRootFamilyQuotientMap ρ) = g := by
    apply Ideal.Quotient.ringHom_ext
    rfl
  let l := completionLift (R ⧸ compatibleRootFamilyIdeal ρ) T p q
  have hl : l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
    change l.comp ((algebraMap _ _).comp (compatibleRootFamilyQuotientMap ρ)) = g
    rw [← RingHom.comp_assoc, completionLift_comp, hq]
  refine ⟨l, hl, ?_⟩
  intro k hk
  apply completionLift_unique _ _ _ q k
  apply RingHom.ext
  intro x
  have hsurj : Function.Surjective (compatibleRootFamilyQuotientMap ρ) :=
    Ideal.quotientMap_surjective Function.surjective_id
  obtain ⟨s, rfl⟩ := hsurj x
  exact (RingHom.congr_fun hk s).trans (RingHom.congr_fun hq s).symm

/-- 任意perfectoid試験環への射は、全根族の商のp完備化を一意に経由する。 -/
theorem existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    {T : Type u} [CommRing T] (hT : IsIntegralPerfectoid T p)
    (g : R ⧸ compatibleRootFamilyZeroIdeal ρ →+* T) :
    ∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
      l.comp (compatibleRootFamilyCompletionMap p ρ) = g := by
  let := hT.isReduced T p
  let := hT.isAdicComplete T p
  exact existsUnique_compatibleRootFamilyCompletionLift ρ hρ g

omit [Fact p.Prime] in
/-- 任意根族商は、p前完備な基底からの全射によりp前完備。 -/
theorem compatibleRootFamilyQuotient_isPrecomplete (ρ : σ → ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    IsPrecomplete (Ideal.span {(p : R ⧸ compatibleRootFamilyIdeal ρ)})
      (R ⧸ compatibleRootFamilyIdeal ρ) := by
  let J := compatibleRootFamilyIdeal ρ
  let Q := R ⧸ J
  have h : IsPrecomplete (Ideal.span {(p : R)}) Q :=
    isPrecomplete_of_surjective (Ideal.span {(p : R)}) J.mkQ (Submodule.mkQ_surjective J)
  have hh := (IsPrecomplete.map_algebraMap_iff
    (I := Ideal.span {(p : R)}) (S := Q) (M := Q)).mpr h
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using hh

omit [Fact p.Prime] in
/-- 任意根族商のp完備化への具体的標準射は全射。 -/
theorem compatibleRootFamilyCompletionMap_surjective (ρ : σ → ℕ → R)
    [IsPrecomplete (Ideal.span {(p : R)}) R] :
    Function.Surjective (compatibleRootFamilyCompletionMap p ρ) := by
  let := compatibleRootFamilyQuotient_isPrecomplete (p := p) ρ
  have hc : Function.Surjective
      (algebraMap (R ⧸ compatibleRootFamilyIdeal ρ) (CompatibleRootFamilyCompletion p ρ)) :=
    AdicCompletion.of_surjective _ _
  have hq : Function.Surjective (compatibleRootFamilyQuotientMap ρ) :=
    Ideal.quotientMap_surjective Function.surjective_id
  exact hc.comp hq

/-- 候補のperfectoid性が得られれば、任意根族の具体的標準射はperfectoid化。 -/
theorem compatibleRootFamilyCompletionMap_isPerfectoidization_of_isIntegralPerfectoid
    (ρ : σ → ℕ → R) (hρ : ∀ s n, ρ s (n + 1) ^ p = ρ s n)
    (hC : IsIntegralPerfectoid (CompatibleRootFamilyCompletion p ρ) p) :
    IsPerfectoidization p (compatibleRootFamilyCompletionMap p ρ) := by
  refine ⟨hC, ?_⟩
  intro T _ hT g
  exact existsUnique_compatibleRootFamilyCompletionLift_to_perfectoid ρ hρ hT g

end SerrePositivity.BhattScholze

end CompatibleRootFamilyQuotient
