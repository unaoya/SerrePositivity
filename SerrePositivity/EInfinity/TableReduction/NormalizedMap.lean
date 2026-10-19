module

public import SerrePositivity.EInfinity.TableReduction.SequenceDegeneracy
public import SerrePositivity.EInfinity.TableReduction.DegreeMap
public import SerrePositivity.EInfinity.BarrattEccles.Generators
public import SerrePositivity.EInfinity.BarrattEccles.Nondegenerate
public import SerrePositivity.EInfinity.BarrattEccles.BasisAction

/-!
# 正規化鎖の全生成元上の table reduction

概要：Berger–Fresse §1.4.1 の退化列の消滅と正規化鎖の生成元上の式を構成する。
方針：非退化単体では既存基底を使い、退化単体では両辺の消滅を使う。
規約：自然数の鎖次数で計算し、コチェイン次数 −d との比較同型を介する。
使われ方：TR の微分保存を、全ての置換列の交代境界の公式へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.TableReduction

open CategoryTheory Surjection
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：退化単体の頂点列で table reduction は零（BF §1.4.1）。
方針：非退化単体の隣接非一致による特徴づけを否定して隣接一致を得る。
規約：nullary と次数零も含む。
使われ方：正規化鎖上の像の計算で退化項を除く。 -/
lemma onSequence_eq_zero_of_degenerate (n d : ℕ)
    (x : (BarrattEccles.simplicial n) _⦋d⦌)
    (hx : x ∈ (BarrattEccles.simplicial n).degenerate d) :
    onSequence A (BarrattEccles.simplexEquiv n d x) = 0 := by
  classical
  have hnot : ¬ x ∈ (BarrattEccles.simplicial n).nonDegenerate d := by
    simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hx
  rw [BarrattEccles.mem_nonDegenerate_iff] at hnot
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  exact onSequence_eq_zero_of_adjacent_eq A _ i.castSucc i.succ rfl (not_ne_iff.mp hi)

/-- 概要：自然数次数の正規化 BE 鎖からの TR の線形写像（BF §1.4.1）。
方針：コチェイン次数 −d の次数写像を比較同型の逆と合成する。
規約：まだ微分の保存は仮定も主張もしない。
使われ方：正規化生成元の交代境界で微分保存を証明する。 -/
def normalizedMap (n d : ℕ) :
    (BarrattEccles.normalizedChains A n).X d →ₗ[A] degreeModule A n d :=
  (degreeMap A n d).comp (BarrattEccles.complexXIso A n d).inv.hom

/-- 概要：全ての置換列の正規化生成元の像は table の有限和（BF §1.4.1）。
方針：非退化なら基底で比較し、退化なら両辺を零とする。
規約：退化する面を含む式にもそのまま適用できる。
使われ方：TR の鎖写像性の全生成元での計算式となる。 -/
lemma normalizedMap_generator (n d : ℕ) (x : (BarrattEccles.simplicial n) _⦋d⦌) :
    normalizedMap A n d (BarrattEccles.normalizedGenerator A n d x) =
      onSequence A (BarrattEccles.simplexEquiv n d x) := by
  classical
  unfold normalizedMap
  simp only [LinearMap.comp_apply]
  by_cases hx : x ∈ (BarrattEccles.simplicial n).nonDegenerate d
  · have hgen := BarrattEccles.complexXIso_basis A n d ⟨x, hx⟩
    rw [← hgen]
    change degreeMap A n d
      ((BarrattEccles.complexXIso A n d).toLinearEquiv.symm
        ((BarrattEccles.complexXIso A n d).toLinearEquiv
          (BarrattEccles.complexBasis A n d (ULift.up ⟨x, hx⟩)))) = _
    rw [LinearEquiv.symm_apply_apply, degreeMap_basis]
  · have hdeg : x ∈ (BarrattEccles.simplicial n).degenerate d := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hx
    rw [BarrattEccles.normalizedGenerator_degenerate A n d x hdeg, map_zero, map_zero,
      onSequence_eq_zero_of_degenerate A n d x hdeg]

/-- 概要：実際の BE 次数成分からの TR は置換同変（BF §1.3.6）。
方針：既存の BE 基底上の右作用の式と置換列の TR の同変性を使う。
規約：BE の共変な対称列は σ⁻¹ の右乗法。
使われ方：TR を対称列の射へ束ねる成分の等式となる。 -/
lemma degreeMap_action (n d : ℕ) (σ : Equiv.Perm (Fin n)) :
    (degreeMap A n d).comp
        ((BarrattEccles.complexRightAction A n σ⁻¹).f (-(d : ℤ))).hom =
      (renameLinear A σ).comp (degreeMap A n d) := by
  apply (BarrattEccles.complexBasis A n d).ext
  intro x
  simp only [LinearMap.comp_apply]
  rw [BarrattEccles.complexBasis_rightAction, degreeMap_basis, degreeMap_basis]
  change onSequence A (fun i => BarrattEccles.simplexEquiv n d x.down.val i * σ⁻¹) = _
  exact onSequence_action A _ σ

end SerrePositivity.EInfinity.TableReduction
