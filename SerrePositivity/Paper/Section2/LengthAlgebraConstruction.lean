module

public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.Paper.Section2.PerfectQuotientLimit
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# 定理2.5の標数別の未完了部分

両分岐とも一つの代数上で全てのパラメータ系を扱い、冪と階数の公式は共通の導出に任せる。
等標数では perfection・塔の作用・共通分母・商の長さの極限比較まで構成済み。
`sorry` の内容は極限値の重複度との同定と正次数の Koszul ホモロジーの消滅である。
混標数の `sorry` は CLMST の帰結を現在の塔へ移す部分を含む。
これらは定理2.5の完成を意味しない。仮定をまとめる独自の構造体やクラスは使わない。
-/

public section
universe u
open IsLocalRing
open scoped ENNReal
namespace SerrePositivity.Section2

/-- 具体的な perfection 上の長さの性質のうち、残る未証明部分。
共通分母は `exists_tower_perfection_conductor` で、正則基底の正規性を導いて構成する。
`PrimaryParameters` は分母と合わせて有限長の商を定める `h-1` 個の元を準素イデアル内で選ぶ。
`PerfectQuotientLimit.lean` の
`normalized_frobenius_length_tendsto_perfection_quotient_of_primary` は、
それらを既存の近似環の核・像の長さ評価に適用し、
通常の Frobenius 商の正規化した長さが perfection の商の正規化長さへ収束することを証明した。
任意の両立する塔作用での `towerLengthOn` への移送も、
`normalized_frobenius_length_tendsto_towerLengthOn_quotient` で証明済み。

残るのは Monsky・Roberts の結果との接続による極限値の Hilbert–Samuel 重複度との同定、
正次数の Koszul ホモロジーの正規化長さの消滅。
代数自体の存在ではなく、標準写像で定まる `D_perf` のこれらの性質を未証明入力として残す。 -/
theorem perfectClosure_length_properties_pending (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p]
    (e : A ≃+* MvPowerSeries (Fin h) (ResidueField D))
    (he : ∀ i, e (t i) = MvPowerSeries.X i)
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p) :
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          (koszulHomologySelf (fun j ↦ algebraMap D (PerfectClosure D p) (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          ((PerfectClosure D p) ⧸
            Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  sorry

/-- 等標数の長さ代数として Mathlib の `PerfectClosure D p` を選ぶ。
塔の作用と二つの係数制限の両立は証明済み。長さの性質だけを上の未証明入力から受け取る。 -/
theorem lengthAlgebra_equalCharacteristic (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p]
    (e : A ≃+* MvPowerSeries (Fin h) (ResidueField D))
    (he : ∀ i, e (t i) = MvPowerSeries.X i) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra D C)
      (_ : Algebra (Tower A t p) C) (_ : IsScalarTower A D C)
      (_ : IsScalarTower A (Tower A t p) C),
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p C).len
          (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  let : Algebra D (PerfectClosure D p) := (PerfectClosure.of D p).toAlgebra
  let : Algebra A (PerfectClosure D p) :=
    ((PerfectClosure.of D p).comp (algebraMap A D)).toAlgebra
  let : IsScalarTower A D (PerfectClosure D p) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra (Tower A t p) (PerfectClosure D p) :=
    (towerToPerfect A (PerfectClosure D p) t p).toRingHom.toAlgebra
  let : IsScalarTower A (Tower A t p) (PerfectClosure D p) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      ((towerToPerfect A (PerfectClosure D p) t p).commutes x).symm
  refine ⟨PerfectClosure D p, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  exact perfectClosure_length_properties_pending A D hinj hsep hres t hdimA hdimD
    hpos ht hsop p e he rfl

/-- 混標数版の引用と接続の未完了部分。
CLMST（arXiv:2209.04046v4）Notation 4.0.1、Cor. 4.0.4、Prop. 4.0.10、4.0.14 の
帰結を、非完備の塔に係数制限した形。perfectoidization の構成と完備化の比較は未実装。
基底は Witt 冪級数環で、最初のパラメータが `p` であることを明示する。 -/
theorem lengthAlgebra_mixedCharacteristic_pending (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharZero D] (htp : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p (ResidueField D)))
    (he : ∀ (i : Fin h) (hi : (i : ℕ) ≠ 0), e (t i) = MvPowerSeries.X ⟨i, hi⟩) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra D C)
      (_ : Algebra (Tower A t p) C) (_ : IsScalarTower A D C)
      (_ : IsScalarTower A (Tower A t p) C),
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p C).len
          (koszulHomologySelf (fun j ↦ algebraMap D C (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p C).len
          (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  sorry

end SerrePositivity.Section2
