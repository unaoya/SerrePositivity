module

public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.Paper.Section2.PerfectApproximationLength
public import SerrePositivity.Paper.Section2.PerfectConductor
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# 定理2.5の標数別の未完了部分

両分岐とも一つの代数上で全てのパラメータ系を扱い、冪と階数の公式は共通の導出に任せる。
等標数の `sorry` は引用だけではなく、トレース・誤差評価の未実装部分も含む。perfection と塔の作用は構成済み。
混標数の `sorry` は CLMST の帰結を現在の塔へ移す部分を含む。
これらは定理2.5の完成を意味しない。仮定をまとめる独自の構造体やクラスは使わない。
-/

public section
universe u
open IsLocalRing
open scoped ENNReal
namespace SerrePositivity.Section2

/-- 具体的な perfection 上の長さの性質。Monsky・Roberts の結果との接続、
共通分母に必要な基底環の正規性、誤差評価用の元の選択と極限への接続、
Koszul の重複度公式の適用は未完了。
部分代数の増大・被覆、分母を与えた場合の核の評価は
`PerfectApproximation` で証明済み。テンソル積と近似部分代数の同型は
`PerfectBaseChange` で証明済み。近似環の商の正規化長さを `D` 上の通常の長さに戻す
有限段の公式は `PerfectApproximationLength` で証明済み。
さらに、`H` 内の `h-1` 個の元と分母 `g` が有限長の商を定めれば、
分母の根を加えた近似環の商の長さが零へ収束することも証明済み。
初段の共通分母も与えれば、商写像の核の長さの零への収束と、
核・像の長さの和を Frobenius 商の長さで表す等式も証明済み。
像の増大・被覆と長さの上限性も接続済みで、共通分母と元の組を与えれば
通常の Frobenius 商の正規化した長さは perfection の商の正規化長さへ収束する。
この元の組の存在、文献による極限値の同定、正次数の Koszul ホモロジーの消滅は未完了。
トレース双対基底による共通分母の一般論は `TraceConductor` で証明済み。
正規な基底から塔の正規性を導く一般論も証明済み。
元の環内からの分数体基底の選択と、有限拡大から分数体の有限次元性を導く部分も証明済み。
具体的な分数体の代数構造を整え、基底環の正規性を前提とした共通分母の存在を
`exists_tower_perfection_conductor_of_normal_base` で証明済み。
論文の基底の正規性を現行の仮定から導く部分は未完了であり、本定理の仮定は増やしていない。
体の係数拡大の同型・基底の移送とトレースによる分母の一般論の接続は証明済みである。
初段の分母から全ての段の分母への移行と塔の完全性は `PerfectConductor` で証明済み。
代数自体の存在ではなく、標準写像で定まる `D_perf` の性質を未証明入力として残す。
塔の作用は完全性から一意に決まるため、基底の作用との両立を仮定すればよい。 -/
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
