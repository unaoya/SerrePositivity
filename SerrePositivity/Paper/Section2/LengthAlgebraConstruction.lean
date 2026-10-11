module

public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.Paper.Section2.PerfectQuotientLimit
public import SerrePositivity.Paper.Section2.PerfectKoszulLimit
public import SerrePositivity.Paper.Section2.MixedLengthAlgebra
public import SerrePositivity.Inputs.RobertsFrobenius
public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# 定理2.5の標数別の構成

両分岐とも一つの代数上で全てのパラメータ系を扱い、冪と階数の公式は共通の導出に任せる。
等標数では perfection・塔の作用・共通分母・商の長さの極限比較まで構成済み。
Koszul ホモロジーの有限段の長さ公式、一様な冪ねじれ、有向極限との同型も証明済み。
Roberts の消滅定理を名前付きの引用として適用し、perfection 上の高次の長さの消滅と
商の長さの重複度との同定を導出した。等標数の構成自身には直接の `sorry` はないが、
Roberts・正規化長さの引用と、重複度公式の未証明入力への依存は残る。正則パラメータは証明済み。
混標数では根の塔を `p` 進完備化し、基底変更した有限代数の perfectoid 化を取る。
CLMST の引用と冪ねじれの確認・係数制限を組み合わせて、同じ二性質を導く。
両標数の接続に直接の `sorry` はないが、外部引用そのものの証明は残る。
仮定をまとめる独自の構造体やクラスは使わない。
-/

public section
universe u
open IsLocalRing CategoryTheory Limits
open scoped ENNReal
namespace SerrePositivity.Section2

/-- 高次 Frobenius Koszul ホモロジーの消滅極限から、等標数の長さ代数の二性質を導く。
有向極限による高次の消滅と、Euler 公式による零次の重複度との同定を組み合わせる。
消滅極限そのものは明示した前提であり、ここで新たな未証明入力を導入しない。 -/
theorem perfectClosure_length_properties_of_higher_tendsto
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p]
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (hlim : ∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
      Filter.Tendsto (fun n : ℕ ↦
        (Module.length D (koszulHomologySelf (fun j ↦ z j ^ (p ^ n)) i) : ℝ≥0∞) /
          (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          (koszulHomologySelf (fun j ↦ algebraMap D (PerfectClosure D p) (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          ((PerfectClosure D p) ⧸
            Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  constructor
  · intro z hz i hi
    exact towerLengthOn_perfection_koszulHomology_eq_zero_of_tendsto A D p t ht hdimA
      hinj hres hsep hcanonical z hz i (hlim z hz i hi)
  · intro z hz
    apply towerLengthOn_perfection_parameter_quotient_eq_multiplicity_of_higher_tendsto
      A D p t ht hdimA hdimD hpos hinj hres hsep hcanonical z hz
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -(j : ℤ) := ⟨(-i).toNat, by omega⟩
    exact hlim z hz j (by omega)

/-- 一般の有限自由複体に対する Roberts 型の消滅定理から、等標数の長さ代数の二性質を導く。
Koszul 複体への適用条件・Frobenius 基底変更・実数値からの変換を前段の定理で確認する。
Roberts の定理自体は明示的な仮定であり、既存の未証明入力を増やさない。 -/
theorem perfectClosure_length_properties_of_roberts
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p]
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (hRoberts : ∀ d : ℕ, ringKrullDim D = d →
      ∀ K : CochainComplex (ModuleCat.{u} D) ℤ,
        (∀ j, Module.Free D (K.X j) ∧ Module.Finite D (K.X j)) →
        (∀ j, j < -(d : ℤ) ∨ 0 < j → IsZero (K.X j)) →
        (∀ j, IsFiniteLength D (K.homology j)) →
        ∀ i : ℕ, 0 < i → Filter.Tendsto (fun n : ℕ ↦
          ((Module.length D
            ((baseChange (iterateFrobenius D p n) K).homology (-(i : ℤ)))).toNat : ℝ) /
              (p : ℝ) ^ (n * d)) Filter.atTop (nhds 0)) :
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ i : ℕ, 0 < i →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          (koszulHomologySelf (fun j ↦ algebraMap D (PerfectClosure D p) (z j)) i) = 0) ∧
      (∀ (z : Fin h → D), IsSystemOfParameters D z →
        (towerLengthOn A D hinj t p (PerfectClosure D p)).len
          ((PerfectClosure D p) ⧸
            Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) =
          ENNReal.ofReal
            (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ)) := by
  apply perfectClosure_length_properties_of_higher_tendsto A D hinj hsep hres t
    hdimA hdimD hpos ht p hcanonical
  intro z hz i hi
  simpa only [stageRank, Nat.cast_pow] using
    normalized_frobenius_koszul_tendsto_of_homology_vanishing D p hRoberts z hz i hi

/-- Roberts の引用定理から導く、具体的な perfection 上の長さの二性質。
共通分母は `exists_tower_perfection_conductor` で、正則基底の正規性を導いて構成する。
`PrimaryParameters` は分母と合わせて有限長の商を定める `h-1` 個の元を準素イデアル内で選ぶ。
`PerfectQuotientLimit.lean` の
`normalized_frobenius_length_tendsto_perfection_quotient_of_primary` は、
それらを既存の近似環の核・像の長さ評価に適用し、
通常の Frobenius 商の正規化した長さが perfection の商の正規化長さへ収束することを証明した。
任意の両立する塔作用での `towerLengthOn` への移送も、
`normalized_frobenius_length_tendsto_towerLengthOn_quotient` で証明済み。

`PerfectKoszulLength.lean` は近似環のホモロジーの長さを
`ℓ_D H^i(z^(p^n); D) / p^(nh)` と同定し、全段・全次数で一様な消去冪も構成する。
`KoszulMultiplicityLimit.lean` は高次のこの値が零へ収束するという前提から、
既存の Koszul Euler 公式と冪の重複度公式を使って商の極限値を同定する。
`towerLengthOn_perfection_parameter_quotient_eq_multiplicity_of_higher_tendsto` は
それを既存の商の極限比較へ接続する。

`PerfectKoszulLimit.lean` はホモロジーと有向極限の可換性を証明し、
消滅極限を任意の両立する塔作用での `λ_D` の消滅へ移す。
`perfectClosure_length_properties_of_higher_tendsto` が二性質を組み合わせる。
`FrobeniusKoszulLimit.lean` は Roberts 型の一般定理の適用条件と値域の変換を確認し、
`perfectClosure_length_properties_of_roberts` が一般定理から二性質までを接続する。
本定理は `Inputs.frobenius_homology_length_tendsto_zero` を適用し、
等標数の残っていた未証明の結論を、この文献の一般定理からの導出に置き換える。
Roberts の定理そのものと既存の一般入力への依存は残る。 -/
theorem perfectClosure_length_properties (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p]
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
  exact perfectClosure_length_properties_of_roberts A D hinj hsep hres t hdimA hdimD
    hpos ht p hcanonical (Inputs.frobenius_homology_length_tendsto_zero D p)

/-- 等標数の長さ代数として Mathlib の `PerfectClosure D p` を選ぶ。
塔の作用と二つの係数制限の両立を構成し、Roberts の引用から導いた長さの性質を適用する。
基底の冪級数環との具体的な同型や、基底パラメータの像がパラメータ系であるとの仮定は不要。 -/
theorem lengthAlgebra_equalCharacteristic (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h)
    (hpos : 0 < h) (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    [CharP D p] :
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
  exact perfectClosure_length_properties A D hinj hsep hres t hdimA hdimD
    hpos ht p rfl

/-- 混標数の長さ代数を、完備化した塔上の perfectoid 化として構成する。
Witt 冪級数環とパラメータの情報から塔の perfectoid 性を供給し、
CLMST の引用から証明した二つの長さの性質を適用する。
普遍対象の存在と文献の性質は名前付き引用に依存し、この接続に直接の `sorry` はない。 -/
theorem lengthAlgebra_mixedCharacteristic (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
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
  have hperf := Inputs.completedTower_isIntegralPerfectoid
    A (ResidueField D) p t hpos htp e he
  refine ⟨MixedPerfectoid A D t p hperf, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ?_⟩
  exact mixedPerfectoid_length_properties A D hinj hres t hdimA hdimD
    hpos ht hsop p htp e he hperf

end SerrePositivity.Section2
