module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.IndexedNumeratorIdeal
public import SerrePositivity.AlgebraicGeometry.BlowupChartIdeals
public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover

/-!
概要：KST §5、Stacks 080Y の Noether アフィン基底上の blowup 中心の有限チャートによる降下。
方針：中心の有限生成族を選び、実際のイデアル層の整合チャート族に分子候補中心の生成性を適用する。
規約：降下は例外イデアルの正の冪による捻りを含むチャート等式として述べる。
使われ方：blowup の合成を基底上の一つの blowup で支配する準備。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：Noether アフィン基底の blowup 上の中心は、有限チャート被覆上で十分大きい各次数の基礎環イデアルから得られる。
方針：有限生成族のチャート被覆と整合チャートイデアルの同次数での生成性を組み合わせる。
規約：KST §5、Stacks 080Y、各基底イデアルは有限生成で Iᴰ に含まれる。
使われ方：中心の降下のアフィン局所版と合成の支配。
-/
theorem exists_finite_chart_ideal_descent [IsNoetherianRing R]
    (K : (affineBlowup I).IdealSheafData) :
    ∃ (ι : Type u) (C : ι → I), Finite ι ∧
      Ideal.span (Set.range (fun i => (C i).1)) = I ∧
      (⨆ i, affineBlowupChart I (C i) = ⊤) ∧
      ∃ N : ℕ, ∀ D ≥ N, ∃ J : Ideal R, J.FG ∧ J ≤ I ^ D ∧
        ∀ i, J.map (chartBaseMap I (C i)) =
          Ideal.span {chartBaseMap I (C i) (C i).1 ^ D} * blowupChartIdeal I K (C i) := by
  classical
  obtain ⟨s, hs⟩ := Ideal.fg_of_isNoetherianRing I
  have hmem (r : ↥s) : r.1 ∈ I := hs ▸ Ideal.subset_span r.2
  let C (r : ↥s) : I := ⟨r.1, hmem r⟩
  have hCrange : Set.range (fun i => (C i).1) = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact i.2
    · intro hr
      exact ⟨⟨r, hr⟩, rfl⟩
  have hC : Ideal.span (Set.range (fun i => (C i).1)) = I := by
    rw [hCrange]
    exact hs
  obtain ⟨N, hN⟩ := indexedNumeratorIdeal_map_eventually I (blowupChartIdeal I K) C
    (blowupChartIdeals_compatible I K) (fun i => blowupChartIdeal_fg I K (C i))
  refine ⟨↥s, C, inferInstance, hC, iSup_affineBlowup_generatorCharts I C hC, N,
    fun D hD => ?_⟩
  exact ⟨indexedNumeratorIdeal I (blowupChartIdeal I K) C D,
    Ideal.fg_of_isNoetherianRing _, indexedNumeratorIdeal_le I _ C D, hN D hD⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
