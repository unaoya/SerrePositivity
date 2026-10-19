module

public import SerrePositivity.EInfinity.TableReduction.CanonicalValue
public import SerrePositivity.EInfinity.TableReduction.NormalizedMap

/-!
# Table reduction の全次数での全射性

概要：Berger–Fresse §1.3.4・§1.4.2–3 の一般の TR の全射性を構成的に証明する。
方針：全射語を対応する非退化 BE 基底へ送り、次数ごとの線形な切断へ延長する。
規約：全 arity・全次数・任意の可換環を含み、まだ鎖写像性は使わない。
使われ方：微分保存から χ の平方零とオペラッド公理を導くときの全射性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open Surjection

variable (A : Type u) [CommRing A]

/-- 概要：標準非退化単体の基底での TR の値（BF §1.4.3）。
方針：次数写像の基底の式を標準頂点列の値へ簡約する。
規約：nullary 空語も含む。
使われ方：次数ごとの切断の合成が恒等であることを示す。 -/
lemma degreeMap_canonical_basis {n d : ℕ} (v : BasisWord n d) :
    degreeMap A n d
      (BarrattEccles.complexBasis A n d (ULift.up (canonicalNondegenerateSimplex v))) =
        basis A n d (ULift.up v) := by
  rw [degreeMap_basis]
  change onSequence A (BarrattEccles.simplexEquiv n d (canonicalSimplex v)) = _
  rw [simplexEquiv_canonicalSimplex, onSequence_canonical, generator_word]

/-- 概要：各次数の TR の線形な切断（BF §1.4.2–3）。
方針：全射語の自由基底を標準非退化 BE 単体の基底へ送る。
規約：この切断が微分や部分合成を保つとは主張しない。
使われ方：TR の全射性を全ての係数環で直接与える。 -/
def degreeSection (n d : ℕ) :
    degreeModule A n d →ₗ[A] (BarrattEccles.complex A n).X (-(d : ℤ)) :=
  (basis A n d).constr A (fun v =>
    BarrattEccles.complexBasis A n d (ULift.up (canonicalNondegenerateSimplex v.down)))

/-- 概要：TR と次数ごとの切断の合成は恒等（BF §1.4.3）。
方針：全射語の自由基底の各元で比較する。
規約：線形写像としての等式。
使われ方：全射性と後続の平方零の証明で逆像を指定する。 -/
lemma degreeMap_comp_section (n d : ℕ) :
    (degreeMap A n d).comp (degreeSection A n d) = LinearMap.id := by
  apply (basis A n d).ext
  intro v
  obtain ⟨v⟩ := v
  simp only [LinearMap.comp_apply, degreeSection, Module.Basis.constr_basis,
    degreeMap_canonical_basis, LinearMap.id_apply]

/-- 概要：実際の BE 複体の各次数からの TR は全射（BF §1.3.4）。
方針：切断の像を指定した元の逆像とする。
規約：任意の可換環・全 arity・全鎖次数。
使われ方：TR の微分保存と部分合成保存から χ の公理を導く。 -/
lemma degreeMap_surjective (n d : ℕ) : Function.Surjective (degreeMap A n d) := by
  intro y
  refine ⟨degreeSection A n d y, ?_⟩
  exact LinearMap.congr_fun (degreeMap_comp_section A n d) y

/-- 概要：自然数次数の正規化 BE 鎖からの TR も全射（BF §1.3.4）。
方針：コチェイン次数 −d の逆像を正規化鎖との同型で移す。
規約：鎖写像性を仮定しない。
使われ方：生成元の交代境界の式から平方零を導くための全射性。 -/
lemma normalizedMap_surjective (n d : ℕ) : Function.Surjective (normalizedMap A n d) := by
  intro y
  obtain ⟨x, hx⟩ := degreeMap_surjective A n d y
  refine ⟨(BarrattEccles.complexXIso A n d).hom x, ?_⟩
  change degreeMap A n d ((BarrattEccles.complexXIso A n d).toLinearEquiv.symm
    ((BarrattEccles.complexXIso A n d).toLinearEquiv x)) = y
  rw [LinearEquiv.symm_apply_apply, hx]

end SerrePositivity.EInfinity.TableReduction
