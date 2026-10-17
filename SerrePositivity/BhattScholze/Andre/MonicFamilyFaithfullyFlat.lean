module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyColimit
public import SerrePositivity.BhattScholze.Andre.MonicFiniteFamilyFlat
public import SerrePositivity.BhattScholze.Andre.Transfinite.FaithfullyFlatColimit

/-!
# André E1・E2：任意モニック族の通常根商の忠実平坦性

## 概要

任意個の正次数モニック多項式に独立な根を添加した通常の関係商は、元の係数環上忠実平坦。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の通常代数部分を扱う。

## 方針

有限部分族の自由忠実平坦性と、固定基底上の忠実平坦代数の有向余極限の既存定理を使う。
全族の実関係商との R 代数同型を通じて元の係数作用の忠実平坦性を得る。

## 規約

零係数環と任意濃度の族を許す。自由加群の余極限の自由性は推論しない。
完備化・perfectoid 化後の忠実平坦性はこの通常代数の結果には含めない。
原典の Prop 7.11 の経路と異なる、明示的商と有限部分族の余極限による計算である。

## 使われ方

pd 計算の係数商に現れる任意モニック族の通常商の忠実平坦性を供給する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {R σ : Type u} [CommRing R]

/-- 概要：正次数モニック族の有限商余極限は元の係数環上忠実平坦。
方針：各有限商の忠実平坦性と、R 代数の有向余極限の忠実平坦性を適用する。
規約：遷移射の単射性は不要であり、全族の有限性は要求しない。
使われ方：BS Thm 7.14（著者版 p.61）の任意同時根添加の通常忠実平坦性。 -/
theorem monicFamilyColimit_faithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat R (PolynomialFamilyColimit f) := by
  apply Transfinite.faithfullyFlat_algebraDirectLimit
    (fun T : Finset σ => PolynomialFamilyFiniteStage f T)
    (fun _ _ h => polynomialFamilyFiniteMap f h)
  intro T
  exact (monicFiniteFamilyQuotient_free_faithfullyFlat (fun t : T => f t)
    (fun t => hf t) (fun t => hdeg t)).2

/-- 概要：任意正次数モニック族の全関係を課した実通常商は元の係数環上忠実平坦。
方針：有限商余極限との R 代数同型で忠実平坦性を移す。
規約：元の標準係数射に関して述べ、零係数環を排除しない。
使われ方：BS Rem 7.15（著者版 p.62）の通常モニック係数商の忠実平坦性入力。 -/
theorem polynomialFamilyQuotient_faithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat R (PolynomialFamilyQuotient f) := by
  let := monicFamilyColimit_faithfullyFlat f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R (PolynomialFamilyColimit f)
    (polynomialFamilyColimitEquiv f).symm.toLinearEquiv

/-- 概要：任意正次数モニック族の根を同時に持つ通常忠実平坦拡大が同じ宇宙に存在する。
方針：全族の標準関係商と標準根を取る。
規約：perfectoid 性・完備性・p 完全忠実平坦性は結論しない。
使われ方：BS Thm 7.14（著者版 p.61）の通常同時根添加部分の公開結果。 -/
theorem exists_familyMonicRootedFaithfullyFlat (f : σ → Polynomial R)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    ∃ (T : Type u) (_ : CommRing T) (φ : R →+* T) (ρ : σ → T),
      (letI := φ.toAlgebra; Module.FaithfullyFlat R T) ∧
        ∀ s, (f s).eval₂ φ (ρ s) = 0 := by
  refine ⟨PolynomialFamilyQuotient f, inferInstance, algebraMap R _,
    polynomialFamilyQuotientRoot f, ?_, polynomialFamilyQuotient_eval f⟩
  rw [toAlgebra_algebraMap]
  exact polynomialFamilyQuotient_faithfullyFlat f hf hdeg

end SerrePositivity.BhattScholze.Andre
