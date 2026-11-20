module

public import SerrePositivity.AlgebraicGeometry.AffineCenterDescent
public import SerrePositivity.AlgebraicGeometry.IdealSheafLocality

/-!
概要：KST §5、Stacks 080Y の Noether アフィン基底上での中心の降下のイデアル層等式。
方針：有限標準チャートの降下等式を実際のイデアル層の逆像と例外イデアルの冪へ移す。
規約：降下対象は与えられた blowup 上のイデアル層であり、別の中心の存在を仮定しない。
使われ方：blowup の合成を一つの blowup で支配するための中心の構成。
-/

@[expose] public noncomputable section

universe u
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：通常のアフィン blowup 上の中心イデアルの逆像イデアル層。
方針：基底環の中心を Spec のイデアル層へ移し、構造射で引き戻す。
規約：KST §5、Stacks 080Y、例外閉部分スキームの定義イデアル。
使われ方：降下する中心へ例外イデアルの冪を掛ける。
-/
def affineExceptionalIdealSheaf : (affineBlowup I).IdealSheafData :=
  ((specIdealEquiv (.of R)).symm I).comap (affineBlowupπ I)

set_option backward.isDefEq.respectTransparency false in
/--
概要：基底のイデアル層の逆像のチャートイデアルは環の拡大イデアル。
方針：構造射のチャート公式と Spec の逆像のイデアル対応を使う。
規約：KST §5、Stacks 080Y、任意の基底イデアル J を許す。
使われ方：構成した降下イデアルのチャート上の評価。
-/
theorem blowupChartIdeal_base_comap (J : Ideal R) (a : I) :
    blowupChartIdeal I (((specIdealEquiv (.of R)).symm J).comap (affineBlowupπ I)) a =
      J.map (chartBaseMap I a) := by
  unfold blowupChartIdeal
  rw [← Scheme.IdealSheafData.comap_comp]
  have hπ : affineBlowupChartι I a ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := affineBlowupChartIso_inv_ι_π I a
  rw [hπ, specIdealEquiv_comap, OrderIso.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
概要：blowup 上の中心イデアル層の積のチャートイデアルは積を保つ。
方針：開埋め込みによる逆像と Spec のイデアル対応の乗法性を使う。
規約：KST §5、Stacks 080Y、任意のイデアル層を許す。
使われ方：例外イデアルの冪による捻りのチャート計算。
-/
theorem blowupChartIdeal_mul (K L : (affineBlowup I).IdealSheafData) (a : I) :
    blowupChartIdeal I (K * L) a = blowupChartIdeal I K a * blowupChartIdeal I L a := by
  unfold blowupChartIdeal
  rw [idealSheaf_comap_mul_of_openImmersion, specIdealEquiv_mul]

set_option backward.isDefEq.respectTransparency false in
/--
概要：中心イデアル層の自然数冪のチャートイデアルは冪を保つ。
方針：開制限と Spec のイデアル対応の冪保存を使う。
規約：KST §5、Stacks 080Y、零乗を含む。
使われ方：降下次数 D の例外イデアルの評価。
-/
theorem blowupChartIdeal_pow (K : (affineBlowup I).IdealSheafData) (n : ℕ) (a : I) :
    blowupChartIdeal I (K ^ n) a = blowupChartIdeal I K a ^ n := by
  unfold blowupChartIdeal
  rw [idealSheaf_comap_pow_of_openImmersion, specIdealEquiv_pow]

/--
概要：例外イデアル層のチャートイデアルは a の係数像の単項イデアル。
方針：基底イデアルの逆像公式と拡大中心の単項性を使う。
規約：KST §5、Stacks 080Y、実際の例外イデアル。
使われ方：降下イデアルのチャート等式を大域の捻りへ移す。
-/
theorem affineExceptionalIdealSheaf_chart (a : I) :
    blowupChartIdeal I (affineExceptionalIdealSheaf I) a =
      Ideal.span {chartBaseMap I a a.1} := by
  rw [affineExceptionalIdealSheaf, blowupChartIdeal_base_comap, chart_map_ideal_eq_span]

set_option backward.isDefEq.respectTransparency false in
/--
概要：Noether アフィン基底の blowup 上の任意の中心は、例外イデアルの十分大きい冪を掛けると基底から降下する。
方針：有限チャートで構成した基底イデアルを使い、実際のイデアル層の等式を開被覆で検出する。
規約：KST §5、Stacks 080Y、各次数 D で有限生成な J ⊆ Iᴰ を構成する。
使われ方：blowup の合成の支配に使う実際の降下中心。
-/
theorem exists_affine_center_descent [IsNoetherianRing R]
    (K : (affineBlowup I).IdealSheafData) :
    ∃ N : ℕ, ∀ D ≥ N, ∃ J : Ideal R, J.FG ∧ J ≤ I ^ D ∧
      ((specIdealEquiv (.of R)).symm J).comap (affineBlowupπ I) =
        affineExceptionalIdealSheaf I ^ D * K := by
  obtain ⟨ι, C, hfinite, hC, _, N, hN⟩ := exists_finite_chart_ideal_descent I K
  let : Finite ι := hfinite
  refine ⟨N, fun D hD => ?_⟩
  obtain ⟨J, hJfg, hJle, hJ⟩ := hN D hD
  refine ⟨J, hJfg, hJle, ?_⟩
  apply idealSheaf_ext_of_affineOpenCover (affineBlowupGeneratorChartCover I C hC)
  intro i
  apply (specIdealEquiv (.of (BlowupChartRing I (C i)))).injective
  change blowupChartIdeal I (((specIdealEquiv (.of R)).symm J).comap (affineBlowupπ I)) (C i) =
    blowupChartIdeal I (affineExceptionalIdealSheaf I ^ D * K) (C i)
  rw [blowupChartIdeal_base_comap, blowupChartIdeal_mul, blowupChartIdeal_pow,
    affineExceptionalIdealSheaf_chart, Ideal.span_singleton_pow]
  exact hJ i

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
