module

public import SerrePositivity.BhattScholze.Andre.Transfinite.PerfectoidLimitCompleteness
public import SerrePositivity.BhattScholze.Andre.Transfinite.PresentationColimit
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidDistinguishedKernel
public import SerrePositivity.BhattScholze.Prism.Perfectoid.FontaineKernelNaturality
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality
public import SerrePositivity.CommutativeAlgebra.WittLiftUniqueness
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta
open SerrePositivity SerrePositivity.BhattScholze
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (p : ℕ) [Fact p.Prime]
/-- ## 概要
環準同型が誘導する Fontaine 環の標準写像を定める。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
mod p の写像を Perfection と WittVector に順に移す。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
def ainfMap {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (f : R →+* S) :
    WittVector p (PreTilt R p) →+* WittVector p (PreTilt S p) :=
  WittVector.map (Perfection.map p (modPMap p f))
/-- ## 概要
恒等環準同型が誘導する Fontaine 環の写像は恒等である。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
Witt 係数と Perfection の係数を順に比較する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_id {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    (x : WittVector p (PreTilt R p)) : ainfMap p (RingHom.id R) x = x := by
  apply WittVector.ext
  intro n
  simp only [ainfMap, WittVector.map_coeff]
  apply Perfection.ext
  intro m
  change modPMap p (RingHom.id R) (PreTilt.coeff m (x.coeff n)) =
    PreTilt.coeff m (x.coeff n)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff m (x.coeff n))
  rw [← hr]
  rfl
/-- ## 概要
Fontaine 環の標準写像は環準同型の合成を保つ。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
各 Witt 係数の各 Perfection 成分を mod p の代表元で比較する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] [Fact (¬ IsUnit (p : T))]
    (f : R →+* S) (g : S →+* T) (x : WittVector p (PreTilt R p)) :
    ainfMap p (g.comp f) x = ainfMap p g (ainfMap p f x) := by
  apply WittVector.ext
  intro n
  simp only [ainfMap, WittVector.map_coeff]
  apply Perfection.ext
  intro m
  change modPMap p (g.comp f) (PreTilt.coeff m (x.coeff n)) =
    modPMap p g (modPMap p f (PreTilt.coeff m (x.coeff n)))
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (PreTilt.coeff m (x.coeff n))
  rw [← hr]
  rfl


/-- ## 概要
Fontaine 環の標準写像は標準 δ 構造を保つ。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
既存の完全係数環上の Witt 写像の δ 自然性を適用する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem ainfMap_delta {R S : Type u} [CommRing R] [CommRing S]
    [Fact (¬ IsUnit (p : R))] [Fact (¬ IsUnit (p : S))] (f : R →+* S) :
    (wittDeltaStructure p (PreTilt R p)).IsDeltaHom
      (wittDeltaStructure p (PreTilt S p)) (ainfMap p f) :=
  wittDeltaStructure_map_isDeltaHom p (PreTilt R p) (Perfection.map p (modPMap p f))

variable {ι : Type u} [Preorder ι] (R : ι → Type u) [∀ i, CommRing (R i)]
    [∀ i, Fact (¬ IsUnit (p : R i))]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
/-- ## 概要
環の有向系から Fontaine 環の有向系を得る。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
標準写像の恒等と合成の公式に元の有向系の公理を適用する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
instance ainfSystem : DirectedSystem (fun i ↦ WittVector p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap p (f i j h)) where
  map_self := by
    intro i x
    have he : f i i le_rfl = RingHom.id (R i) := by ext y; exact DirectedSystem.map_self' f y
    rw [he]
    exact ainfMap_id p x
  map_map := by
    intro k j i hij hjk x
    have he : f i k (hij.trans hjk) = (f j k hjk).comp (f i j hij) := by
      ext y
      exact (DirectedSystem.map_map' f hij hjk y).symm
    rw [he]
    exact (ainfMap_comp p _ _ x).symm


include f in
 private theorem perfectoid_limit [OrderBot ι] [IsDirectedOrder ι]
    [∀ i, IsAdicComplete (Ideal.span {(p : R i)}) (R i)]
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
  obtain ⟨π, v, he⟩ := (hdata ⊥).1
  obtain ⟨d, hd, hk⟩ := exists_distinguished_fontaine_kernel_generator (R ⊥) p
    (hdata ⊥).2.1 (hdata ⊥).2.2 π v he
  have hd0 : WittVector.fontaineTheta (R ⊥) p d = 0 := by
    apply RingHom.mem_ker.mp
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  apply isIntegralPerfectoid_adicCompletion_of_presentationDiagram
    (fun i ↦ WittVector p (PreTilt (R i) p)) R
    (fun i j h ↦ ainfMap p (f i j h)) f
    (fun i ↦ WittVector.fontaineTheta (R i) p)
    (fun i j h ↦ fontaineTheta_natural p (f i j h))
    (fun i ↦ wittDeltaStructure p (PreTilt (R i) p))
    (fun i j h ↦ ainfMap_delta p (f i j h))
    (fun i ↦ wittDeltaStructure_isPerfect p (PreTilt (R i) p)) d hd
  · intro i x
    exact surjective_fontaineTheta (hdata i).2.1 x
  · intro i
    exact fontaineKernel_eq_span_image_distinguished p (f ⊥ i bot_le) d hd hd0 (hdata i).2.2


end SerrePositivity.BhattScholze.Andre.Transfinite
namespace SerrePositivity.BhattScholze.Andre.Transfinite

/-- ## 概要
最小元を持つ有向添字上の perfectoid 環の有向系について、環余極限の p 進完備化は perfectoid である。
BS Lemma 3.9（著者版 pp.31–32）、Thm 3.10（p.32）、Thm 7.14（p.61）の極限操作を補足する。

## 方針
各段の Fontaine 全射を自然性により余極限へ移す。最小段の distinguished 核生成元の像が
全段の核を生成するので、余極限も完全 δ 環の distinguished 商となる。零環の場合は別に処理する。

## 規約
環と添字は Type u とする。p 正則性や遷移射の単射性は要求しない。

## 使われ方
超限塔の可算共終性を持つ極限段の perfectoid 性を供給する。
-/
theorem isIntegralPerfectoid_adicCompletion_ringDirectLimit {p : ℕ} [Fact p.Prime]
    {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
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
  exact perfectoid_limit p R f hR
/-- ## 概要
perfectoid 環の p 完全忠実平坦な有向系で、添字の可算部分集合が上界を持つとき、
環余極限自体が perfectoid となる。BS Thm 7.14（著者版 p.61）の非可算共終性の極限段。

## 方針
可算データの降下から余極限の p 進完備性を得て、標準完備化との環同型により
完備化の perfectoid 性を余極限自身に移す。

## 規約
最小元を持つ有向添字を用いる。零環と p ねじれを許す。環と添字は Type u。

## 使われ方
ω₁ の終段で完備化を追加せず perfectoid 環を得る。
-/
theorem isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound
    {p : ℕ} [Fact p.Prime] {ι : Type u} [Preorder ι] [OrderBot ι] [IsDirectedOrder ι]
    (R : ι → Type u) [∀ i, CommRing (R i)]
    (f : ∀ i j, i ≤ j → R i →+* R j)
    [DirectedSystem R (fun i j h ↦ f i j h)]
    (hR : ∀ i, IsIntegralPerfectoid (R i) p)
    (hflat : ∀ i j h, let := (f i j h).toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R i)}) (R j))
    (hbound : ∀ s : Set ι, s.Countable → ∃ j, ∀ i ∈ s, i ≤ j) :
    IsIntegralPerfectoid (Ring.DirectLimit R (fun i j h ↦ f i j h)) p := by
  let L := Ring.DirectLimit R (fun i j h ↦ f i j h)
  let := isAdicComplete_directLimit_of_perfectoid_completelyFaithfullyFlat R f p hR hflat hbound
  exact isIntegralPerfectoid_of_ringEquiv p
    (AdicCompletion.ofAlgEquiv (Ideal.span {(p : L)})).symm.toRingEquiv
    (isIntegralPerfectoid_adicCompletion_ringDirectLimit R f hR)

end SerrePositivity.BhattScholze.Andre.Transfinite
