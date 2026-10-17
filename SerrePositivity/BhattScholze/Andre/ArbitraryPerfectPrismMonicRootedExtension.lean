module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismMonicCandidate
public import SerrePositivity.BhattScholze.Andre.ArbitraryPerfectPrismMonicPerfectoidCompletelyFlat

/-!
# André E1・E2：完全 prism 商上の任意モニック族の根付き拡大

## 概要

完全 prism の商上の任意正次数モニック族には、全ての多項式の根を持つ
p 完全忠実平坦な整 perfectoid 拡大がある。
BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の一段構成。

## 方針

同次数モニック lift を固定し、既存候補の標準基底射の完全忠実平坦性を適用する。
商の係数射で評価を移して、元の多項式族の根を得る。
原典の Prop 7.11 を使う証明とは異なる PD 先行構成と具体的比較による経路である。

## 規約

正次数を明示する。添字型全体に有限性を仮定しない。

## 使われ方

一般の perfectoid 基底への移送で、任意族の一段拡大を供給する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
local notation "R" => A ⧸ Ideal.span {OrientedPrism.generator P}
include hP

set_option maxHeartbeats 800000 in
-- 同じ候補の完備化台環と標準係数作用を含む存在証人の定義展開に必要。
/-- 概要：完全 prism 商上の任意正次数モニック族の全根を同じ p 完全忠実平坦拡大に得る。
方針：同次数モニック lift に候補の平坦性を適用し、評価の自然性で根を降ろす。
規約：添字型は任意で、補助的な平坦性仮定を要求しない。
使われ方：BS Thm 7.14（著者版 p.61）、Rem 7.15（p.62）の別証明の一段構成。 -/
theorem exists_monicRootedPerfectoidExtension_of_perfectPrism
    (f : σ → Polynomial R) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  let F := perfectPrismMonicLift P f hf
  have hF : ∀ s, (F s).Monic := fun s => (perfectPrismMonicLift_spec P f hf s).2
  have hFdeg : ∀ s, 0 < (F s).natDegree := by
    intro s
    rw [(perfectPrismMonicLift_spec P f hf s).1]
    exact hdeg s
  let D := P.deltaStructure
  let d := P.generator
  let hd := OrientedPrism.isDistinguished_of_perfect P hP
  let := polynomialPrismCommRing D d F
  let φ := polynomialPerfectoidCandidateBaseMap D d F hd
  let ρ := polynomialPerfectoidCandidateRoot D d F hd
  refine ⟨PolynomialPerfectoidCandidate D d F hd, inferInstance, φ, ρ,
    polynomialPerfectoidCandidate_isIntegralPerfectoid D d F hd,
    perfectPrismMonicPerfectoidBaseMap_isCompletelyFaithfullyFlat_arbitrary P hP F hF hFdeg, ?_⟩
  intro s
  rw [← perfectPrismMonicLift_map P f hf s, Polynomial.eval₂_map]
  exact polynomialPerfectoidCandidate_eval D d F hd s

end SerrePositivity.BhattScholze.Andre
