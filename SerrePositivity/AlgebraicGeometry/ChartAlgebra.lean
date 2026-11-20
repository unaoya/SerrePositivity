module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.Blowup

/-!
概要：KST §5 のアフィン blowup の標準チャート環を計算する。
方針：斉次局所化内の b/a を実際の分数として構成する。
規約：a は基礎環の非零因子と仮定しない。
使われ方：例外イデアルの局所単項生成と有効 Cartier 性。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.AlgebraicGeometry

open Polynomial HomogeneousLocalization _root_.AlgebraicGeometry CategoryTheory

variable {R : Type u} [CommRing R] (I : Ideal R)

/--
概要：a ∈ I に対する標準 blowup チャート環。
方針：Rees 代数を a t で斉次局所化する。
規約：KST §5、局所化の零次部分を取る。
使われ方：標準開集合の環論的計算。
-/
abbrev BlowupChartRing (a : I) := Away (reesGrade I) (reesDegreeOne I a)

/--
概要：基礎環から標準 blowup チャート環への構造準同型。
方針：定数多項式を斉次局所化に送る。
規約：KST §5 の構造射の環準同型。
使われ方：中心のイデアルをチャート上に拡大する。
-/
def chartBaseMap (a : I) : R →+* BlowupChartRing I a :=
  (fromZeroRingHom (reesGrade I) (.powers (reesDegreeOne I a))).comp
    (reesZeroEquiv I).symm.toRingHom

/--
概要：チャートの係数写像は通常の Rees 局所化への係数写像に一致する。
方針：分母一の分数を代数写像に書き換える。
規約：KST §5、斉次局所化から通常の局所化への単射で比較する。
使われ方：生成元の非零因子性の局所化計算。
-/
lemma chartBaseMap_val (a : I) (r : R) :
    (chartBaseMap I a r).val =
      algebraMap (reesAlgebra I) (Localization.Away (reesDegreeOne I a))
        (algebraMap R (reesAlgebra I) r) := by
  change Localization.mk (algebraMap R (reesAlgebra I) r) 1 = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_one]

set_option backward.isDefEq.respectTransparency false in
/--
概要：標準チャートの構造射はチャートの係数写像の Spec と一致する。
方針：Proj の構造射の局所計算と Spec の反変合成則を使う。
規約：KST §5、チャートの Spec 同型の逆向きを始域に置く。
使われ方：チャート上のイデアル計算を例外閉部分スキームに接続する。
-/
@[reassoc] theorem affineBlowupChartIso_inv_ι_π (a : I) :
    (affineBlowupChartIso I a).inv ≫ (affineBlowupChart I a).ι ≫ affineBlowupπ I =
      Spec.map (CommRingCat.ofHom (chartBaseMap I a)) := by
  unfold affineBlowupπ
  simp only [← Category.assoc]
  rw [show (affineBlowupChartIso I a).inv ≫ (affineBlowupChart I a).ι =
    Proj.awayι (reesGrade I) _ (reesDegreeOne_mem I a) (by decide) from rfl]
  rw [Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/--
概要：チャート環内の生成元の比 b/a。
方針：同次数の分数 (b t)/(a t) を構成する。
規約：KST §5、a と b はともに I の元。
使われ方：中心の拡大イデアルが a で生成されることを証明する。
-/
def chartRatio (a b : I) : BlowupChartRing I a :=
  Away.mk (reesGrade I) (reesDegreeOne_mem I a) 1 (reesDegreeOne I b)
    (by simpa using reesDegreeOne_mem I b)

/--
概要：チャート内では a · (b/a) = b。
方針：分数を共通分母に直し、多項式の交換則を使う。
規約：KST §5、a = 0 の空チャートも含む。
使われ方：例外イデアルの単項生成。
-/
lemma chartBaseMap_mul_ratio (a b : I) :
    chartBaseMap I a a.1 * chartRatio I a b = chartBaseMap I a b.1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, chartBaseMap_val, chartBaseMap_val]
  simp only [chartRatio, Away.val_mk, Localization.mk_eq_mk']
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, ← IsLocalization.mk'_one
    (M := Submonoid.powers (reesDegreeOne I a))
    (Localization.Away (reesDegreeOne I a)) (algebraMap R (reesAlgebra I) b.1)]
  apply IsLocalization.mk'_eq_iff_eq.mpr
  congr 1
  apply Subtype.ext
  simp [reesDegreeOne, reesMonomial, mul_comm]

/--
概要：中心のイデアルのチャート上への拡大は a の単項イデアル。
方針：各 b ∈ I を a · (b/a) と書き、逆包含には a ∈ I を使う。
規約：KST §5、拡大イデアルは環準同型による `Ideal.map`。
使われ方：例外因子の可逆イデアルの局所生成元。
-/
theorem chart_map_ideal_eq_span (a : I) :
    I.map (chartBaseMap I a) = Ideal.span {chartBaseMap I a a.1} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBaseMap I a b ∈ Ideal.span {chartBaseMap I a a.1}
    rw [← chartBaseMap_mul_ratio I a ⟨b, hb⟩]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ a.2

/--
概要：標準 blowup チャート内では中心の生成元 a は非零因子。
方針：a による消滅を多項式変数 t で掛け、可逆化した a t による消滅にする。
規約：KST §5、基礎環内での a の非零因子性は仮定しない。
使われ方：単項な例外イデアルを有効 Cartier イデアルにする局所計算。
-/
theorem chartBaseMap_mem_nonZeroDivisors (a : I) :
    chartBaseMap I a a.1 ∈ nonZeroDivisors (BlowupChartRing I a) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro z hz
  apply HomogeneousLocalization.val_injective
  rw [val_zero]
  have hz' : algebraMap (reesAlgebra I) (Localization.Away (reesDegreeOne I a))
      (algebraMap R (reesAlgebra I) a.1) * z.val = 0 := by
    simpa only [val_mul, chartBaseMap_val, val_zero] using congrArg val hz
  obtain ⟨p, s, hp⟩ := IsLocalization.exists_mk'_eq
    (Submonoid.powers (reesDegreeOne I a)) z.val
  rw [← hp, IsLocalization.mul_mk'_eq_mk'_of_mul] at hz'
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp hz'
  rw [← hp]
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨c * ⟨reesDegreeOne I a, ⟨1, pow_one _⟩⟩, ?_⟩
  apply Subtype.ext
  have hc' : ((c.1 : reesAlgebra I) : R[X]) * (C a.1 * (p : R[X])) = 0 :=
    congrArg (fun q : reesAlgebra I => (q : R[X])) hc
  change (c.1 : R[X]) * (reesDegreeOne I a : R[X]) * (p : R[X]) = 0
  calc
    _ = X * ((c.1 : R[X]) * (C a.1 * (p : R[X]))) := by
      simp only [reesDegreeOne, reesMonomial, ← C_mul_X_pow_eq_monomial, pow_one]
      ring
    _ = 0 := by rw [hc', mul_zero]

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
