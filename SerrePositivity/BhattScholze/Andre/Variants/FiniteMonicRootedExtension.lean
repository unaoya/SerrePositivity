module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicRootedExtension
public import SerrePositivity.BhattScholze.Andre.Variants.MonicRootedBaseEquiv
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectoidTrialPrism

/-!
# André E1・E2：任意の整 perfectoid 基底上の有限モニック根付き拡大

## 概要

任意の整 perfectoid 環上の有限正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一段の有限版。

## 方針

非零枝では Fontaine 写像の核の実 PD 完備化から完全 prism 商表示を得る。
商表示へ多項式を移して有限族の構成を適用し、環同型に沿って基底作用と根を戻す。
零枝は自己拡大を使う。原典の Prop 7.11 による証明とは異なる PD 計算の経路である。

## 規約

各多項式に正次数を要求する。有限性以外に基底の表示・p 正則性・ねじれなしを仮定しない。

## 使われ方

任意族への有向余極限と p 完備化を構成する前の一元・有限族の存在結果。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：任意の整 perfectoid 基底上の有限正次数モニック族に、全根を持つ拡大がある。
方針：完全 prism 商表示で有限族を構成し、基底環同型と評価の自然性で戻す。
規約：全列挙以外に補助的な忠実平坦性や基底表示を仮定しない。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一段構成の有限版。 -/
theorem exists_finiteMonicRootedPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) {m : ℕ} (eσ : Fin m ≃ σ) :
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
      exists_finiteMonicRootedPerfectoidExtension_of_perfectPrism P hP F hFm hFd eσ
    let := hT
    exact ⟨T, hT, g.comp e.symm.toRingHom, ρ,
      monicRootedExtension_of_baseEquiv p e.symm f g ρ hperf hflat hroot⟩

/-- 概要：有限添字型で与えられた正次数モニック族に同じ根付き拡大が存在する。
方針：Fin による全列挙を選び、一般基底上の有限族構成を適用する。
規約：有限性は命題の型クラスで与え、根の添字型は元のままに保つ。
使われ方：BS Rem 7.15（著者版 p.62）の任意有限部分族の根添加。 -/
theorem exists_monicRootedPerfectoidExtension_of_finite
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    {σ : Type u} [Finite σ] (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let := Fintype.ofFinite σ
  exact exists_finiteMonicRootedPerfectoidExtension R p hR f hf hdeg (Fintype.equivFin σ).symm

/-- 概要：任意の整 perfectoid 環上の正次数モニック多項式に、根を持つ拡大がある。
方針：一元族に一般基底上の有限族の存在定理を適用する。
規約：基底環への追加条件を課さず、同じ p に関する完全忠実平坦性を結論する。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一元根添加。 -/
theorem exists_monicRootPerfectoidExtension
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : Polynomial R) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      f.eval₂ φ ρ = 0 := by
  obtain ⟨T, hT, φ, ρ, hperf, hflat, hroot⟩ :=
    exists_monicRootedPerfectoidExtension_of_finite R p hR
      (fun _ : PUnit.{u + 1} => f) (fun _ => hf) (fun _ => hdeg)
  exact ⟨T, hT, φ, ρ PUnit.unit, hperf, hflat, hroot PUnit.unit⟩

end SerrePositivity.BhattScholze.Andre
