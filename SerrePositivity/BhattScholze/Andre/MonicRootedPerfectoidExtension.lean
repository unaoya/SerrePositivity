module

public import SerrePositivity.BhattScholze.Andre.ArbitraryPerfectPrismMonicRootedExtension
public import SerrePositivity.BhattScholze.Andre.MonicRootedBaseEquiv
public import SerrePositivity.BhattScholze.Prism.PerfectoidTrialPrism

/-!
# André E1・E2：任意の整 perfectoid 基底上のモニック根付き拡大

## 概要

任意の整 perfectoid 環上の任意正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一段構成。

## 方針

非零枝では Fontaine 写像の核の実 PD 完備化から完全 prism 商表示を得る。
商表示へ多項式を移して任意族の構成を適用し、環同型に沿って基底作用と根を戻す。
零枝は自己拡大を使う。原典の Prop 7.11 による証明とは異なる PD 計算の経路である。

## 規約

各多項式に正次数を要求する。基底の表示・p 正則性・ねじれなし、族全体の有限性を仮定しない。

## 使われ方

有界深さ有限部分族の実余極限と完備化を使う、一段の全根添加を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：任意の整 perfectoid 基底上の任意正次数モニック族に、全根を持つ拡大がある。
方針：完全 prism 商表示で任意族の拡大を構成し、基底環同型と評価の自然性で戻す。
規約：補助的な忠実平坦性や基底表示、族全体の有限性を仮定しない。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一段構成。 -/
theorem exists_monicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  rcases hR with hs | ⟨hp, hc, ⟨π, v, hv⟩, hF, hker⟩
  · let := hs
    refine ⟨R, inferInstance, RingHom.id R, fun _ => 0, Or.inl hs, ?_, ?_⟩
    · exact monicRootedBase_self_isCompletelyFaithfullyFlat _
    · intro s
      exact Subsingleton.elim _ _
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π v hv
    let := pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    let F := fun s => (f s).map e.symm.toRingHom
    have hFm : ∀ s, (F s).Monic := fun s => (hf s).map _
    have hFd : ∀ s, 0 < (F s).natDegree := by
      intro s
      rw [Polynomial.natDegree_map_eq_of_injective e.symm.injective]
      exact hdeg s
    obtain ⟨T, hT, g, ρ, hperf, hflat, hroot⟩ :=
      exists_monicRootedPerfectoidExtension_of_perfectPrism P hP F hFm hFd
    let := hT
    exact ⟨T, hT, g.comp e.symm.toRingHom, ρ,
      monicRootedExtension_of_baseEquiv p e.symm f g ρ hperf hflat hroot⟩

end SerrePositivity.BhattScholze.Andre
