module

public import SerrePositivity.AlgebraicGeometry.FreeCoverNumeratorCenter
public import SerrePositivity.AlgebraicGeometry.ChartFreeBoundary
public import SerrePositivity.AlgebraicGeometry.IdealFlattening
public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover

/-!
概要：KST §5、Stacks 0815 の境界外で平坦な加群を自由な場合へ還元する被覆。
方針：自由化係数の分子中心を選び、その生成元チャートの境界外を自由にする。
規約：この段階の加群の自由性は境界を可逆化したチャートについてのもの。
使われ方：各生成元チャート上の局所平坦化中心の選択。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R : Type*} [CommRing R] (f : R)

/--
概要：自由化係数の分子を中心の実際の生成元として扱う。
方針：分子中心の生成集合への所属を使う。
規約：KST §5、Stacks 0815、添字は係数の有限集合の部分型。
使われ方：最初の blowup の有限チャート被覆。
-/
def freeCoverNumeratorGenerator (s : Finset (Localization.Away f)) (i : s) :
    freeCoverNumeratorIdeal f s :=
  ⟨(IsLocalization.Away.sec f i.val).1, Ideal.subset_span ⟨i, rfl⟩⟩

/--
概要：分子に対応する有限個の標準チャートは分子中心の blowup 全体を覆う。
方針：中心の定義通りの生成族の被覆性を使う。
規約：KST §5、Stacks 0815、空の係数族による空の blowup も含む。
使われ方：チャートごとの局所平坦化を大域化する。
-/
theorem iSup_freeCoverNumerator_charts (s : Finset (Localization.Away f)) :
    ⨆ i : s, affineBlowupChart (freeCoverNumeratorIdeal f s)
      (freeCoverNumeratorGenerator f s i) = ⊤ :=
  iSup_affineBlowup_generatorCharts (freeCoverNumeratorIdeal f s)
    (freeCoverNumeratorGenerator f s) rfl

/--
概要：境界外で有限表示平坦な加群に、生成元チャートの境界外を自由にする最初の admissible 中心を選ぶ。
方針：局所化先の自由な有限被覆の分子中心を選び、自由性を各チャートの境界外へ移す。
規約：KST §5、Stacks 0815、元の加群とその局所化写像を入力する。
使われ方：自由な場合の平坦化を各チャートへ適用する準備。
-/
theorem exists_initialFreeBoundary_center {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module (Localization.Away f) N] [IsScalarTower R (Localization.Away f) N]
    [Module.FinitePresentation (Localization.Away f) N] [Module.Flat (Localization.Away f) N]
    (μ : M →ₗ[R] N) [IsLocalizedModule.Away f μ] :
    ∃ s : Finset (Localization.Away f), (freeCoverNumeratorIdeal f s).FG ∧
      PrimeSpectrum.basicOpen f ≤ affineCenterComplement (freeCoverNumeratorIdeal f s) ∧
      ∀ i : s,
        let I := freeCoverNumeratorIdeal f s
        let a := freeCoverNumeratorGenerator f s i
        letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
        Module.Free (Localization.Away (chartBaseMap I a f))
          (LocalizedModule.Away (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  obtain ⟨s, hfree, n, hn⟩ := exists_freeCoverNumeratorCenter f N
  refine ⟨s, freeCoverNumeratorIdeal_fg f s,
    basicOpen_le_affineCenterComplement_of_pow_mem (freeCoverNumeratorIdeal f s) f n hn, ?_⟩
  intro i
  have : Module.Free (Localization.Away i.val) (LocalizedModule.Away i.val N) := hfree i
  exact chart_free_away_boundary_of_free_localization
    (freeCoverNumeratorIdeal f s) (freeCoverNumeratorGenerator f s i) f n hn μ i.val rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
