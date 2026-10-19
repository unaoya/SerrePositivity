module

public import SerrePositivity.KST.Comparison.RelativeLocalCoefficients

/-!
# 相対二・三セルの鎖複体の相殺

概要：次数 2・3 にのみ支持された複体の可逆な境界写像から非輪状性を証明する。
方針：次数 2 では全射性、次数 3 では単射性、他では零対象を使う。
規約：Weibel K-book IV.1.5 の plus の相対複体の中間計算。
使われ方：実際のセル添付の相対複体を同定した後のホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：次数 2・3 にのみ支持された複体の境界が同型なら非輪状である。
方針：二つの残る次数で短複体の完全性を確認する。
規約：セル添付がこの複体を持つという主張は含めない。
使われ方：plus の局所係数の相対二・三セルの相殺。
-/
theorem twoCellComplex_acyclic (K : ChainComplex AddCommGrpCat.{u} ℕ)
    (hz : ∀ n : ℕ, n ≠ 2 → n ≠ 3 → IsZero (K.X n)) [IsIso (K.d 3 2)] :
    K.Acyclic := by
  intro n
  by_cases h₂ : n = 2
  · subst n
    rw [K.exactAt_iff' 3 2 1
      ((ComplexShape.down ℕ).prev_eq' (by decide))
      ((ComplexShape.down ℕ).next_eq' (by decide))]
    exact ((K.sc' 3 2 1).exact_iff_epi ((hz 1 (by decide) (by decide)).eq_of_tgt _ _)).mpr
      (show Epi (K.d 3 2) from inferInstance)
  · by_cases h₃ : n = 3
    · subst n
      rw [K.exactAt_iff' 4 3 2
        ((ComplexShape.down ℕ).prev_eq' (by decide))
        ((ComplexShape.down ℕ).next_eq' (by decide))]
      exact ((K.sc' 4 3 2).exact_iff_mono
        ((hz 4 (by decide) (by decide)).eq_of_src _ _)).mpr (show Mono (K.d 3 2) from inferInstance)
    · exact HomologicalComplex.ExactAt.of_isZero (hz n h₂ h₃)

/--
概要：相対局所係数複体の二・三セルの相殺から包含の同型性を得る。
方針：相対複体の非輪状性と単射の擬同型判定を合成する。
規約：固定した基底の任意の局所係数系。
使われ方：構成したセルの相対複体に対する計算の適用。
-/
theorem overLocalHomologyEquivalence_of_twoCellCancellation {B : SSet.{u}}
    (L : LocalCoefficientSystem B) {X Y : Over B} (i : X ⟶ Y) [Mono i]
    (hz : ∀ n : ℕ, n ≠ 2 → n ≠ 3 →
      IsZero ((relativeOverLocalCoefficientChains L i).X n))
    [IsIso ((relativeOverLocalCoefficientChains L i).d 3 2)] :
    overLocalHomologyEquivalences L i :=
  (overLocalHomologyEquivalence_iff_relative_acyclic L i).mpr (twoCellComplex_acyclic _ hz)

end SerrePositivity.KST.Comparison
