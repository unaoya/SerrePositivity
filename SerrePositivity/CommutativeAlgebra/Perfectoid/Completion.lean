module

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # 完備化を経由する perfectoid 化

## 概要

整 perfectoid 環への環準同型は、古典的な `p` 進完備化へ一意に延長する。したがって完備化の perfectoid 化は、元の環の perfectoid 化でもある。

## 方針

存在定理を引用せず、完備化の普遍性（`IsAdicComplete` への一意な延長）だけを証明する。

## 規約

旧 `CommutativeAlgebra/PerfectoidizationCompletion`。

## 使われ方

BhattScholze の Perfectoidization、CLMST。
-/

@[expose] public noncomputable section

universe u

section PerfectoidizationCompletionPart

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

variable (S T : Type u) [CommRing S] [CommRing T] (p : ℕ)

/-- 環準同型は `p` が生成するイデアルを対応するイデアルへ送る。 -/
theorem pIdeal_map (g : S →+* T) :
    (Ideal.span {(p : S)}).map g = Ideal.span {(p : T)} := by
  simp [Ideal.map_span, Set.image_singleton]

/-- 完備化から目標環の `p^n` 商への写像。 -/
def completionQuotientMap (g : S →+* T) (n : ℕ) :
    AdicCompletion (Ideal.span {(p : S)}) S →+*
      T ⧸ (Ideal.span {(p : T)}) ^ n :=
  (Ideal.quotientMap ((Ideal.span {(p : T)}) ^ n) g (by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, pIdeal_map])).comp
      (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n).toRingHom

/-- 完備化から各 `p^n` 商への写像は、商の遷移写像と両立する。 -/
theorem completionQuotientMap_compatible (g : S →+* T)
    {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : T)}) hle).comp
      (completionQuotientMap S T p g n) = completionQuotientMap S T p g m := by
  ext x
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {(p : S)}) S x
  simp only [completionQuotientMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    Ideal.Quotient.factorPow]
  have ha := a.property hle
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at ha
  apply Ideal.Quotient.eq.mpr
  rw [← map_sub]
  exact (show (Ideal.span {(p : S)}) ^ m ≤
      ((Ideal.span {(p : T)}) ^ m).comap g by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, pIdeal_map]) (by
      simpa using (Ideal.span {(p : S)} ^ m).neg_mem ha)

/-- `p` 進完備な環への写像を、古典的な `p` 進完備化へ延長する。
各 `p^n` を法とする写像を作り、Mathlib の完備性の普遍性を適用する。 -/
def completionLift [IsAdicComplete (Ideal.span {(p : T)}) T] (g : S →+* T) :
    AdicCompletion (Ideal.span {(p : S)}) S →+* T :=
  IsAdicComplete.liftRingHom (Ideal.span {(p : T)})
    (completionQuotientMap S T p g) (completionQuotientMap_compatible S T p g)

/-- 完備化への延長は、元の環の標準像上では元の写像に一致する。 -/
@[simp] theorem completionLift_comp [IsAdicComplete (Ideal.span {(p : T)}) T]
    (g : S →+* T) :
    (completionLift S T p g).comp
      (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) = g := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.span {(p : T)})
  intro n s
  simp [completionLift, completionQuotientMap, AdicCompletion.algebraMap_apply]

/-- 完備化上の任意の延長は、各 `p^n` 商で標準写像と一致する。 -/
theorem completion_map_mod (g : S →+* T)
    (l : AdicCompletion (Ideal.span {(p : S)}) S →+* T)
    (hl : l.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) = g)
    (n : ℕ) (x : AdicCompletion (Ideal.span {(p : S)}) S) :
    Ideal.Quotient.mk ((Ideal.span {(p : T)}) ^ n) (l x) =
      completionQuotientMap S T p g n x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {(p : S)}) S x
  let v := a.val n
  have heval : AdicCompletion.eval (Ideal.span {(p : S)}) S n
      (AdicCompletion.mk _ _ a - algebraMap S _ v) = 0 := by
    change Ideal.Quotient.mk _ (a.val n) - Ideal.Quotient.mk _ (a.val n) = 0
    exact sub_self _
  have hmem : AdicCompletion.mk (Ideal.span {(p : S)}) S a - algebraMap S _ v ∈
      (Ideal.span {(p : S)}) ^ n •
        (⊤ : Submodule S (AdicCompletion (Ideal.span {(p : S)}) S)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton (p : S))]
    exact heval
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hmem
  obtain ⟨y, _, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  have hdiff : l (AdicCompletion.mk _ _ a) - g v ∈ (Ideal.span {(p : T)}) ^ n := by
    rw [← RingHom.congr_fun hl v, RingHom.comp_apply, ← map_sub, ← hy]
    rw [Algebra.smul_def, map_mul, map_pow, map_natCast]
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simpa only [map_pow, map_natCast] using dvd_mul_right ((p : T) ^ n) (l y)
  apply Ideal.Quotient.eq.mpr
  simpa [completionQuotientMap, v] using hdiff

/-- 環準同型としての延長は一意である。
連続性を追加仮定せず、`p^n` 倍を保存することと完備化の核の記述で示す。 -/
theorem completionLift_unique [IsAdicComplete (Ideal.span {(p : T)}) T]
    (g : S →+* T) (l : AdicCompletion (Ideal.span {(p : S)}) S →+* T)
    (hl : l.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) = g) :
    l = completionLift S T p g := by
  apply IsAdicComplete.eq_liftRingHom
  intro n
  ext x
  exact completion_map_mod S T p g l hl n x

namespace IsIntegralPerfectoid

/-- 整 perfectoid 環は、零環の場合も含めて古典的に `p` 進完備である。 -/
theorem isAdicComplete [Fact p.Prime] (hT : IsIntegralPerfectoid T p) :
    IsAdicComplete (Ideal.span {(p : T)}) T := by
  rcases hT with hs | ⟨_, hc, _⟩
  · let : Subsingleton T := hs
    infer_instance
  · exact hc

/-- 整 perfectoid 環への環準同型は、元の環の `p` 進完備化へ一意に延長する。
零環への写像についても、完備性の零環インスタンスで同じ証明が適用できる。 -/
theorem existsUnique_completionLift [Fact p.Prime] (hT : IsIntegralPerfectoid T p)
    (g : S →+* T) :
    ∃! l : AdicCompletion (Ideal.span {(p : S)}) S →+* T,
      l.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) = g := by
  let := hT.isAdicComplete T p
  exact ⟨completionLift S T p g, completionLift_comp S T p g,
    fun l hl ↦ completionLift_unique S T p g l hl⟩

end IsIntegralPerfectoid

namespace IsPerfectoidization

variable {S} {C : Type u} [CommRing C]

/-- 古典的 `p` 進完備化の perfectoid 化は、標準写像との合成により元の環の
perfectoid 化となる。完備化側の存在を元の環へ移すために使う。 -/
theorem of_completion [Fact p.Prime]
    {f : AdicCompletion (Ideal.span {(p : S)}) S →+* C}
    (hf : IsPerfectoidization p f) :
    IsPerfectoidization p
      (f.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S))) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT g
  obtain ⟨g', hg', hgunique⟩ := hT.existsUnique_completionLift S T p g
  obtain ⟨l, hl, hlunique⟩ := hf.2 T hT g'
  refine ⟨l, ?_, ?_⟩
  · change l.comp (f.comp (algebraMap S _)) = g
    rw [← RingHom.comp_assoc, hl, hg']
  · intro k hk
    apply hlunique k
    exact hgunique (k.comp f) (by
      change (k.comp f).comp (algebraMap S _) = g
      rw [RingHom.comp_assoc]
      exact hk)

/-- 元の環の perfectoid 化写像を、同じ目標環への完備化上の写像へ延長する。
完備性のインスタンスは定義内部だけに置く。 -/
def completionMap [Fact p.Prime] {f : S →+* C} (hf : IsPerfectoidization p f) :
    AdicCompletion (Ideal.span {(p : S)}) S →+* C := by
  letI := hf.1.isAdicComplete C p
  exact completionLift S C p f

/-- 延長した perfectoid 化写像は、元の環上では元の perfectoid 化写像に一致する。 -/
@[simp] theorem completionMap_comp [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) :
    (completionMap p hf).comp
      (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) = f := by
  let := hf.1.isAdicComplete C p
  exact completionLift_comp S C p f

/-- 元の環の perfectoid 化は、標準的な一意延長により完備化の perfectoid 化となる。
目標の perfectoid 環を変えず、完備化上の写像の一意性から普遍性を移す。 -/
theorem to_completion [Fact p.Prime] {f : S →+* C}
    (hf : IsPerfectoidization p f) : IsPerfectoidization p (completionMap p hf) := by
  refine ⟨hf.1, ?_⟩
  intro T _ hT g
  let := hT.isAdicComplete T p
  obtain ⟨l, hl, hlunique⟩ := hf.2 T hT
    (g.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)))
  refine ⟨l, ?_, ?_⟩
  · change l.comp (completionMap p hf) = g
    have he : (l.comp (completionMap p hf)).comp
        (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) =
          g.comp (algebraMap S (AdicCompletion (Ideal.span {(p : S)}) S)) := by
      rw [RingHom.comp_assoc, completionMap_comp, hl]
    exact (completionLift_unique S T p _ _ he).trans
      (completionLift_unique S T p _ g rfl).symm
  · intro k hk
    apply hlunique k
    rw [← completionMap_comp p hf, ← RingHom.comp_assoc, hk]

end IsPerfectoidization

end SerrePositivity

end PerfectoidizationCompletionPart
