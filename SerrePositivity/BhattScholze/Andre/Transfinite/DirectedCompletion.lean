module

public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidCompletionColimit
public import SerrePositivity.BhattScholze.Andre.Transfinite.AlgebraColimit
open SerrePositivity SerrePositivity.BhattScholze SerrePositivity.BhattScholze.Andre.Transfinite
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A R : ι → Type u) [∀ i, CommRing (A i)] [∀ i, CommRing (R i)]
    (fA : ∀ i j, i ≤ j → A i →+* A j) (fR : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem A (fun i j h ↦ fA i j h)] [DirectedSystem R (fun i j h ↦ fR i j h)]
    (θ : ∀ i, A i →+* R i)
    (hθ : ∀ i j h, (θ j).comp (fA i j h) = (fR i j h).comp (θ i))
local notation "LA" => Ring.DirectLimit A (fun i j h ↦ fA i j h)
local notation "LR" => Ring.DirectLimit R (fun i j h ↦ fR i j h)
local notation "ofA" => Ring.DirectLimit.of A (fun i j h ↦ fA i j h)
local notation "ofR" => Ring.DirectLimit.of R (fun i j h ↦ fR i j h)
/-- ## 概要
完全 δ 表示の核生成元が一段以降の全段で両立すれば、その像は余極限射の核を生成する。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の極限操作を補足する。

## 方針
核の元を一段に代表し、零となる段と指定の基点段の共通上界へ移して単項核表示を使う。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem presentationLimitMap_ker_of_stage (i₀ : ι) (d : A i₀)
    (hker : ∀ j (h : i₀ ≤ j), RingHom.ker (θ j) = Ideal.span {fA i₀ j h d}) :
    RingHom.ker (presentationLimitMap A R fA fR θ hθ) = Ideal.span {ofA i₀ d} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of z
    have hz' : ofR i (θ i a) = 0 := by
      change presentationLimitMap A R fA fR θ hθ (ofA i a) = 0 at hz
      simpa only [presentationLimitMap_of] using hz
    obtain ⟨j, hij, hj⟩ := Ring.DirectLimit.of.zero_exact hz'
    have hja : θ j (fA i j hij a) = 0 :=
      (RingHom.congr_fun (hθ i j hij) a).trans hj
    obtain ⟨k, hjk, hi₀k⟩ := exists_ge_ge j i₀
    have hka : fA j k hjk (fA i j hij a) ∈ RingHom.ker (θ k) := by
      change θ k (fA j k hjk (fA i j hij a)) = 0
      rw [show θ k (fA j k hjk (fA i j hij a)) = fR j k hjk (θ j (fA i j hij a)) from
        RingHom.congr_fun (hθ j k hjk) _]
      rw [hja, map_zero]
    rw [hker k hi₀k] at hka
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hka
    apply Ideal.mem_span_singleton.mpr
    refine ⟨ofA k b, ?_⟩
    rw [← Ring.DirectLimit.of_f hij a, ← Ring.DirectLimit.of_f hjk (fA i j hij a),
      hb, map_mul, Ring.DirectLimit.of_f]
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    change presentationLimitMap A R fA fR θ hθ (ofA i₀ d) = 0
    rw [presentationLimitMap_of]
    have hd : fA i₀ i₀ le_rfl d ∈ RingHom.ker (θ i₀) := by
      rw [hker i₀ le_rfl]
      exact Ideal.mem_span_singleton_self _
    have hd0 : θ i₀ d = 0 := by
      change θ i₀ (fA i₀ i₀ le_rfl d) = 0 at hd
      simpa only [DirectedSystem.map_self' fA] using hd
    rw [hd0, map_zero]
include hθ in
/-- ## 概要
非空有向系の完全 δ 表示で、一段の distinguished 元の像がその段以降の核を生成すれば、
表示先の余極限の p 進完備化は perfectoid である。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の極限操作を補足する。

## 方針
完全 δ 構造を余極限へ移し、基点段以降の核表示から全体の単項核を同定する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem isIntegralPerfectoid_completion_of_eventual_presentation
    (D : ∀ i, DeltaStructure p (A i))
    (hδ : ∀ i j h, (D i).IsDeltaHom (D j) (fA i j h)) (hD : ∀ i, (D i).IsPerfect)
    (i₀ : ι) (d : A i₀) (hd : (D i₀).IsDistinguished d)
    (hs : ∀ i, Function.Surjective (θ i))
    (hk : ∀ j (h : i₀ ≤ j), RingHom.ker (θ j) = Ideal.span {fA i₀ j h d}) :
    IsIntegralPerfectoid (AdicCompletion (Ideal.span {(p : LR)}) LR) p := by
  let DL := deltaDirectLimitStructure A (fun i j h ↦ fA i j h) D (fun i j h x ↦ hδ i j h x)
  have hDL : DL.IsPerfect := deltaDirectLimit_isPerfect A fA D hδ hD
  have hdL : DL.IsDistinguished (ofA i₀ d) :=
    (deltaDirectLimitOf_isDeltaHom A (fun i j h ↦ fA i j h) D
      (fun i j h x ↦ hδ i j h x) i₀).map_isDistinguished hd
  exact isIntegralPerfectoid_adicCompletion_of_distinguished_kernel DL hDL (ofA i₀ d) hdL
    (presentationLimitMap A R fA fR θ hθ) (presentationLimitMap_surjective A R fA fR θ hθ hs)
    (presentationLimitMap_ker_of_stage A R fA fR θ hθ i₀ d hk)
end SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
各段で p が非単元な perfectoid 環の非空有向系について、余極限の通常 p 進完備化は perfectoid である。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の極限操作を補足する。

## 方針
任意の一段の Fontaine 核の distinguished 生成元を選び、
その段以降に自然性で移して、基点段以降の表示による完備化判定を使う。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
private theorem isIntegralPerfectoid_completion_of_nonunit_directed_system
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Fact (¬ IsUnit (p : R i))]
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
        (Ring.DirectLimit R (fun i j h ↦ f i j h))) p := by
  have hdata (i : ι) :
      (∃ (π : R i) (v : (R i)ˣ), (p : R i) = v * π ^ p) ∧
      Function.Surjective (fun x : ModP (R i) p ↦ x ^ p) ∧
      (RingHom.ker (WittVector.fontaineTheta (R i) p)).IsPrincipal := by
    rcases hR i with hz | ⟨hp, hc, ht, hF, hk⟩
    · let := hz
      exact ((Fact.out : ¬ IsUnit (p : R i)) (isUnit_of_subsingleton _)).elim
    · exact ⟨ht, hF, hk⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨π, v, he⟩ := (hdata i₀).1
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator (R i₀) p
    (hdata i₀).2.1 (hdata i₀).2.2 π v he
  have hd0 : WittVector.fontaineTheta (R i₀) p d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  apply isIntegralPerfectoid_completion_of_eventual_presentation
    (fun i ↦ WittVector p (PreTilt (R i) p)) R
    (fun i j h ↦ ainfMap p (f i j h)) f
    (fun i ↦ WittVector.fontaineTheta (R i) p)
    (fun i j h ↦ fontaineTheta_natural p (f i j h))
    (fun i ↦ wittDeltaStructure p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap_delta p (f i j h))
    (fun i ↦ wittDeltaStructure_isPerfect p (PreTilt (R i) p)) i₀ d hd
  · intro i x
    exact surjective_fontaineTheta (hdata i).2.1 x
  · intro i h
    exact fontaineKernel_eq_span_image_distinguished p (f i₀ i h) d hd hd0 (hdata i).2.2
/-- ## 概要
perfectoid 環の任意の非空有向系の環余極限の通常 p 進完備化は perfectoid である。
BS Thm 7.14（著者版 p.61）、Thm 3.10（p.32）の極限操作を補足する。

## 方針
完備化が非零なら、各段から完備化への標準環射により全段の非零性を得る。
任意の基点段の Fontaine 表示を共通上界へ移す議論を適用する。零環枝は直接処理する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性を要求しない。

## 使われ方
André 反復で使う極限の perfectoid 性を、一般の非空有向系に供給する。
-/
theorem isIntegralPerfectoid_adicCompletion_of_directed_perfectoid
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [Nonempty ι]
    [IsDirectedOrder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p) :
    IsIntegralPerfectoid
      (AdicCompletion (Ideal.span {(p : Ring.DirectLimit R (fun i j h ↦ f i j h))})
        (Ring.DirectLimit R (fun i j h ↦ f i j h))) p := by
  classical
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let C := AdicCompletion (Ideal.span {(p : L)}) L
  rcases subsingleton_or_nontrivial C with hz | hn
  · exact Or.inl hz
  let := hn
  have hdata (i : ι) : ∃ (hp : ¬ IsUnit (p : R i)),
      IsAdicComplete (Ideal.span {(p : R i)}) (R i) := by
    let m : R i →+* C := (algebraMap L C).comp
      (Ring.DirectLimit.of R (fun i j h ↦ f i j h) i)
    let : Nontrivial (R i) := m.domain_nontrivial
    rcases hR i with hz | ⟨hp, hc, _⟩
    · exact (zero_ne_one (Subsingleton.elim (0 : R i) 1)).elim
    · exact ⟨hp, hc⟩
  let : ∀ i, Fact (¬ IsUnit (p : R i)) := fun i ↦ ⟨(hdata i).choose⟩
  let : ∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i) := fun i ↦ (hdata i).choose_spec
  exact isIntegralPerfectoid_completion_of_nonunit_directed_system R f hR
end SerrePositivity.BhattScholze.Andre.Transfinite

namespace SerrePositivity.BhattScholze.Andre.Transfinite
/-- ## 概要
固定基底 B 上の p 完全忠実平坦な perfectoid 代数の非空有向系について、
環余極限の通常 p 進完備化への標準係数射も p 完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の極限操作を補足する。

## 方針
共通係数作用での環余極限の完全忠実平坦性を用い、
perfectoid 各段から得る未完備余極限の p 冪ねじれ境界 1 を完備化の保存定理に入力する。

## 規約
環と添字は Type u。添字の最小元・遷移射の単射性・p 正則性は要求しない。
基底の係数射は元の共通係数射と標準完備化射の合成そのものとする。

## 使われ方
任意の非空有向系の極限と完備化を通して、元の初段上の完全忠実平坦性を保つ。
-/
theorem isCompletelyFaithfullyFlat_completedAlgebraRingDirectLimit
    {B ι : Type u} [CommRing B] [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (S : ι → Type u) [∀ i, CommRing (S i)] [∀ i, Algebra B (S i)]
    (f : ∀ i j, i ≤ j → S i →ₐ[B] S j)
    [DirectedSystem S (fun i j h ↦ f i j h)]
    (p : ℕ) [Fact p.Prime] (hS : ∀ i, IsIntegralPerfectoid (S i) p)
    (hflat : ∀ i, IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) (S i)) :
    let L := Ring.DirectLimit S (fun i j h ↦ (f i j h).toRingHom)
    let C := AdicCompletion (Ideal.span {(p : L)}) L
    letI := ((algebraMap L C).comp (algebraRingDirectLimitBaseMap S f)).toAlgebra
    IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) C := by
  apply isCompletelyFaithfullyFlat_adicCompletion_comp p (algebraRingDirectLimitBaseMap S f)
  · exact isCompletelyFaithfullyFlat_algebraRingDirectLimit S f _ hflat
  · refine ⟨1, ?_⟩
    intro n x hx
    simpa only [pow_one] using ringDirectLimit_p_power_torsion_bound_of_perfectoid S
      (fun i j h ↦ (f i j h).toRingHom) p hS n x hx
end SerrePositivity.BhattScholze.Andre.Transfinite
