module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootedPerfectoidExtension
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfectoidization

/-! # B4：根の割り算包による別証明

## 概要
perfectoid 環の導来 p 完備な全射商の任意の perfectoid 化は全射（Thm 7.4）の、
André の補題を使わない別証明。

## 方針
完全 prism 上で核の元に両立する p 冪根を添加する割り算包を作り、その完備化が
p 完全忠実平坦な perfectoid 拡大になることを示して降下する。

## 規約
主張は B4 と同じ。B4 本体は原典どおり André 経由
（`Semiperfectoid/SemiperfectoidSurjectivity`）。

## 使われ方
主定理の経路では使わない。完全 prism 上の \(X^p-b\) 族の prismatic envelope の計算
（A3 の候補）とともに保存する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S C : Type u}
variable [CommRing R] [CommRing S] [CommRing C]

/-- 任意perfectoid環の導来p完備な全射商の、任意の普遍perfectoid化は全射。
André の補題を使わず、完全 prism 上の根の割り算包から降下する別証明。 -/
theorem surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope
    (hR : IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (hS : DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S))
    (f : S →+* C) (hf : IsPerfectoidization p f) : Function.Surjective f := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let := hs
    let : Subsingleton S := q.codomain_trivial
    let : Subsingleton C := f.codomain_trivial
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, _⟩ := exists_perfectoidTrialPrism R p hF hker π u hu
    let := DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := perfectDeltaPDPrism (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := perfectDeltaPDPrism_isPerfect (wittDeltaStructure p (PreTilt R p))
      (wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    exact surjective_of_isPerfectoidization_of_perfectPrism_quotient P hP
      (q.comp e.toRingHom) (hq.comp e.surjective) hS f hf

end SerrePositivity.BhattScholze
