module

public import SerrePositivity.BhattScholze.Andre.PolynomialPerfectoidCandidate
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# André E1：完全 prism の商からのモニック根候補

## 概要

完全 prism の商上のモニック多項式族を、次数とモニック性を保って prism の台環へ持ち上げ、
具体的な perfectoid 根候補を得る。BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の準備。

## 方針

モニック係数 lift の Mathlib の定理を使い、前工程の多項式族の候補を適用する。
係数商からの基底射を保ったまま評価の自然性で根方程式を移す。
原典の Prop 7.11 による証明とは異なる δ 除算の経路である。

## 規約

候補の忠実平坦性は未証明であり、最終目標を宣言するものではない。
ここでは正次数は不要で、零環の候補を排除しない。

## 使われ方

同じモニック lift の正則性と pd 計算を使い、候補の p 完全忠実平坦性を後で供給する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A)

local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}
local notation "q" => Ideal.Quotient.mk (Ideal.span {OrientedPrism.generator P})

/-- 概要：商上のモニック多項式族を同次数モニックに lift する。
方針：商係数射の全射性とモニック lift の存在定理から選ぶ。
規約：lift の選択を固定し、後の候補と正則性で同じものを使う。
使われ方：BS Rem 7.15（著者版 p.62）の prismatic envelope の関係式。 -/
def perfectPrismMonicLift (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) :
    σ → Polynomial A := fun s =>
  Classical.choose (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))

/-- 概要：固定した lift は係数商射で元の多項式に写る。
方針：lift の選択の証明を取り出す。
規約：基底係数作用を変えない。
使われ方：BS Thm 7.14（著者版 p.61）の元の多項式の根方程式。 -/
theorem perfectPrismMonicLift_map (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (s : σ) :
    (perfectPrismMonicLift P f hf s).map q = f s :=
  (Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))).1

/-- 概要：固定した lift は元の多項式と同じ次数を持つモニックである。
方針：同次数モニック lift の選択の証明を取り出す。
規約：元が正次数なら lift も正次数となる。
使われ方：BS Rem 7.15(1)（著者版 p.62）のモニック商・正則性。 -/
theorem perfectPrismMonicLift_spec (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) (s : σ) :
    (perfectPrismMonicLift P f hf s).natDegree = (f s).natDegree ∧
      (perfectPrismMonicLift P f hf s).Monic :=
  (Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective (f := q) Ideal.Quotient.mk_surjective (f s)) (hf s))).2

/-- 概要：完全 prism の商上のモニック族には、具体的な根を持つ perfectoid 候補がある。
方針：同次数モニック lift の関係式を δ 除算し、商射と評価の自然性で根を降ろす。
規約：p 完全忠実平坦性は未証明であり、零候補を許す。
使われ方：BS Thm 7.14（著者版 p.61）の別経路で同じ候補の平坦性を後で検証する。 -/
theorem exists_monicRootedPerfectoidCandidate_of_perfectPrism
    (hP : P.deltaStructure.IsPerfect)
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧ ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let F := perfectPrismMonicLift P f hf
  let hd := OrientedPrism.isDistinguished_of_perfect P hP
  let D := P.deltaStructure
  let d := P.generator
  let := polynomialPrismCommRing D d F
  let φ := polynomialPerfectoidCandidateBaseMap D d F hd
  let ρ := polynomialPerfectoidCandidateRoot D d F hd
  refine ⟨PolynomialPerfectoidCandidate D d F hd, inferInstance, φ, ρ,
    polynomialPerfectoidCandidate_isIntegralPerfectoid D d F hd, ?_⟩
  intro s
  rw [← perfectPrismMonicLift_map P f hf s, Polynomial.eval₂_map]
  exact polynomialPerfectoidCandidate_eval D d F hd s

end SerrePositivity.BhattScholze.Andre
