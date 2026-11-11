module

public import SerrePositivity.BhattScholze.Semiperfectoid.FontainePrism

/-!
# 固定した A_inf の古典的な prism データ

## 概要
drafts と同じ係数環・θ・δ を使い、有界な完全 prism と剰余同型を作る。
## 方針
非零の枝は既存の完全 prism の Witt 復元を使い、零環の枝は直接作る。
## 規約
BS 著者版 Theorem 3.10・Proposition 7.10。零環を除外する仮定を足さない。
## 使われ方
A3 の AinfData と有限 T・S′ の表示の古典的な入力。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Semiperfectoid
open CategoryTheory DerivedCompletion Prismatic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R]

/-- p が単元である整 perfectoid 環は零環。定義の二つの枝を直接使う。 -/
theorem perfectoid_subsingleton_of_isUnit (hR : IsIntegralPerfectoid R p) (hp : IsUnit (p : R)) :
    Subsingleton R := by
  rcases hR with hs | ⟨hn, _⟩
  · exact hs
  · exact (hn hp).elim

/-- p が非単元の枝の perfectoid 環は、定義どおり古典的に p 完備。 -/
theorem perfectoid_isAdicComplete_of_nonunit [Fact (¬ IsUnit (p : R))]
    (hR : IsIntegralPerfectoid R p) : IsAdicComplete (Ideal.span {(p : R)}) R := by
  rcases hR with hs | ⟨_, hc, _⟩
  · letI := hs
    have hp : IsUnit (p : R) := by
      rw [show (p : R) = 1 from Subsingleton.elim _ _]
      exact isUnit_one
    exact ((Fact.out : ¬ IsUnit (p : R)) hp).elim
  · exact hc

/-- drafts と同じ係数環。零環の枝では R、それ以外では W(R♭)。 -/
def ainfClassicalCoefficients : CommRingCat.{u} := by
  classical
  exact if hp : IsUnit (p : R) then CommRingCat.of R else
    letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    CommRingCat.of (WittVector p (PreTilt R p))

/-- p が単元の枝の係数環の式。 -/
theorem ainfClassicalCoefficients_of_isUnit (hp : IsUnit (p : R)) :
    ainfClassicalCoefficients p R = CommRingCat.of R := by
  simp [ainfClassicalCoefficients, hp]

/-- p が非単元の枝の係数環の式。 -/
theorem ainfClassicalCoefficients_of_nonunit (hp : ¬ IsUnit (p : R)) :
    letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    ainfClassicalCoefficients p R = CommRingCat.of (WittVector p (PreTilt R p)) := by
  simp [ainfClassicalCoefficients, hp]

/-- 固定した A_inf から R への θ。非零の枝は標準 Fontaine 射。 -/
def ainfClassicalTheta (hR : IsIntegralPerfectoid R p) : ainfClassicalCoefficients p R →+* R := by
  classical
  by_cases hp : IsUnit (p : R)
  · rw [ainfClassicalCoefficients_of_isUnit p R hp]
    exact RingHom.id R
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    letI := perfectoid_isAdicComplete_of_nonunit p R hR
    rw [ainfClassicalCoefficients_of_nonunit p R hp]
    exact WittVector.fontaineTheta R p

/-- 固定した A_inf の δ 構造。零環では一意な δ 構造、非零の枝では標準 Witt δ 構造。 -/
def ainfClassicalDelta (hR : IsIntegralPerfectoid R p) : DeltaStructure p (ainfClassicalCoefficients p R) := by
  classical
  by_cases hp : IsUnit (p : R)
  · letI := perfectoid_subsingleton_of_isUnit p R hR hp
    let D : DeltaStructure p R := (DeltaStructure.existsUnique_of_mod_p
      (show Function.Injective (fun x : R => (p : R) * x) from fun _ _ _ => Subsingleton.elim _ _)
      (RingHom.id R) (fun _ => Subsingleton.elim _ _)).choose
    rw [ainfClassicalCoefficients_of_isUnit p R hp]
    exact D
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    rw [ainfClassicalCoefficients_of_nonunit p R hp]
    exact wittDeltaStructure p (PreTilt R p)

/-- 係数環の等式に沿って δ・θ と prism の存在を同時に移す。等式の除去で恒等の場合へ戻す。 -/
private theorem exists_prism_of_cast (C C' : CommRingCat.{u}) (h : C = C')
    (D : DeltaStructure p C') (θ : C' →+* R)
    (h0 : ∃ Q : OrientedPrism p C', Q.deltaStructure = D ∧ Q.deltaStructure.IsPerfect ∧
      IsBoundedPrism Q ∧ ∃ res : C' ⧸ Q.ideal ≃+* R,
        res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) = θ) :
    ∃ Q : OrientedPrism p C,
      Q.deltaStructure = Eq.mpr (congrArg (fun X : CommRingCat.{u} => DeltaStructure p X) h) D ∧
      Q.deltaStructure.IsPerfect ∧ IsBoundedPrism Q ∧ ∃ res : C ⧸ Q.ideal ≃+* R,
        res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) =
          Eq.mpr (congrArg (fun X : CommRingCat.{u} => X →+* R) h) θ := by
  cases h
  exact h0

/-- 概要：固定した係数環・θ・δ で、有界な完全 prism と θ を保つ剰余同型が存在する。
方針：非零の枝を既存の Witt 復元で構成し、零環の枝を直接閉じる。
規約：BS 著者版 Theorem 3.10・Proposition 7.10。drafts の定義と同じ二分岐を使う。
使われ方：A3 の AinfData の古典的な存在と、有限 T・S′ の基底の選択。 -/
theorem exists_ainfClassicalPrism (hR : IsIntegralPerfectoid R p) :
    ∃ Q : OrientedPrism p (ainfClassicalCoefficients p R),
      Q.deltaStructure = ainfClassicalDelta p R hR ∧ Q.deltaStructure.IsPerfect ∧ IsBoundedPrism Q ∧
      ∃ res : ainfClassicalCoefficients p R ⧸ Q.ideal ≃+* R,
        res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) = ainfClassicalTheta p R hR := by
  classical
  by_cases hp : IsUnit (p : R)
  · letI := perfectoid_subsingleton_of_isUnit p R hR hp
    let D : DeltaStructure p R := (DeltaStructure.existsUnique_of_mod_p
      (show Function.Injective (fun x : R => (p : R) * x) from fun _ _ _ => Subsingleton.elim _ _)
      (RingHom.id R) (fun _ => Subsingleton.elim _ _)).choose
    let Q : OrientedPrism p R :=
      ⟨D, 0, fun _ _ _ => Subsingleton.elim _ _,
        isModuleComplete_of_pow_smul_zero R (p : R) (ModuleCat.of R R) 0
          (fun _ => Subsingleton.elim _ _),
        isModuleComplete_of_pow_smul_zero R 0 (ModuleCat.of R R) 0
          (fun _ => Subsingleton.elim _ _),
        by rw [show (p : R) = 0 from Subsingleton.elim _ _]; exact Ideal.zero_mem _⟩
    have hperfect : Q.deltaStructure.IsPerfect :=
      ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
    have hb : IsBoundedPrism Q := ⟨0, fun _ _ _ => Subsingleton.elim _ _⟩
    letI : Unique R := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    letI : Unique (R ⧸ Q.ideal) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    let res : R ⧸ Q.ideal ≃+* R := RingEquiv.ofUnique
    have ht : res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) = RingHom.id R := by
      ext x
      exact Subsingleton.elim _ _
    have hraw : ∃ Q : OrientedPrism p R,
        Q.deltaStructure = D ∧ Q.deltaStructure.IsPerfect ∧ IsBoundedPrism Q ∧
        ∃ res : R ⧸ Q.ideal ≃+* R,
          res.toRingHom.comp (Ideal.Quotient.mk Q.ideal) = RingHom.id R :=
      ⟨Q, rfl, hperfect, hb, res, ht⟩
    have ht := exists_prism_of_cast p R (ainfClassicalCoefficients p R) (CommRingCat.of R)
      (ainfClassicalCoefficients_of_isUnit p R hp) D (RingHom.id R) hraw
    simpa [ainfClassicalDelta, ainfClassicalTheta, hp, D,
      show (p : R) = 1 from Subsingleton.elim _ _] using ht
  · letI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    letI := perfectoid_isAdicComplete_of_nonunit p R hR
    obtain ⟨A, P, hP, hb, ⟨e⟩⟩ := exists_boundedPerfectPrismPresentation p R hR
    have hraw := exists_fontainePrism_of_perfectPresentation P hP hb e
    have ht := exists_prism_of_cast p R (ainfClassicalCoefficients p R)
      (CommRingCat.of (WittVector p (PreTilt R p))) (ainfClassicalCoefficients_of_nonunit p R hp)
      (wittDeltaStructure p (PreTilt R p)) (WittVector.fontaineTheta R p) hraw
    simpa [ainfClassicalDelta, ainfClassicalTheta, hp] using ht

end SerrePositivity.BhattScholze.Semiperfectoid
