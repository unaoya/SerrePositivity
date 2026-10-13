module

public import SerrePositivity.Paper.Section2.PerfectApproximationLength
public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.CommutativeAlgebra.PrimaryParameters
public import SerrePositivity.CommutativeAlgebra.KoszulMultiplicityLimit

/-! # Perfection の商の長さと Frobenius 極限

正則基底の正規性から非零の共通分母を選び、その分母と合わせて有限長の商を作る
`h-1` 個の元を準素イデアル内で選ぶ。既存の近似環の核の誤差評価に適用し、
通常の Frobenius 商の正規化した長さが perfection の商の正規化長さへ収束することを示す。
利用側が分母や誤差評価用の元を与える必要はない。
任意の両立する塔作用は標準作用と一致することを使い、定理2.5の `towerLengthOn` へも移す。

高次 Frobenius Koszul ホモロジーの消滅極限を前提に、商の極限値と
Hilbert–Samuel 重複度との同定も行う。perfection の高次ホモロジーへの移行は
`PerfectKoszulLimit.lean` で証明する。消滅極限自体の供給は定理2.5の残作業である。
証明済みの正則パラメータと正規化長さの既存の引用入力を使い、新しい未証明入力はない。
-/

public section

universe u

namespace SerrePositivity.Section2

open IsLocalRing
open scoped ENNReal

attribute [local instance] towerPerfectionAlgebra

/-- 準素イデアルの Frobenius 商の正規化した長さは、perfection の商の正規化長さへ収束する。
共通分母と誤差評価用の元の組は、正規性と素イデアル回避によって構成する。 -/
theorem normalized_frobenius_length_tendsto_perfection_quotient_of_primary
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A) [Algebra A (PerfectClosure D p)]
    (hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a))
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    (H : Ideal D) (hH : H.radical = maximalIdeal D) :
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop
      (nhds (towerLengthFun A t p ((PerfectClosure D p) ⧸ H.map (PerfectClosure.of D p)))) := by
  obtain ⟨g, hg, hgc⟩ := exists_tower_perfection_conductor D p A t ht hdimA hinj hres hbase hsep
  have hgD : algebraMap A D g ≠ 0 := fun hz ↦ hg (hinj (hz.trans (map_zero _).symm))
  have hr : h - 1 + 1 = h := Nat.sub_add_cancel hpos
  have hd : ringKrullDim D = (h - 1 : ℕ) + 1 := by
    rw [hdimD]
    exact_mod_cast hr.symm
  obtain ⟨z, hz, hfin⟩ := exists_error_parameters_in_primary
    D H hH (algebraMap A D g) hgD hd
  let : IsArtinianRing (D ⧸ maximalIdeal D) :=
    inferInstanceAs (IsArtinianRing (ResidueField D))
  have hHfin : IsFiniteLength D (D ⧸ H) :=
    isFiniteLength_of_le_radical_annihilator (maximalIdeal D) (D ⧸ H) (by
      rw [Ideal.annihilator_quotient, hH])
  exact normalized_frobenius_length_tendsto_perfection_quotient
    A D p t hbase ht hdimA hinj hres hsep H hHfin (algebraMap A D g) hgc hr z hz hfin

/-- 基底の作用と両立する任意の塔作用で、perfection の商の `λ_D` は同じ Frobenius 極限になる。
完全環への塔の写像の一意性で標準作用へ戻し、定理2.5の `towerLengthOn` の形に接続する。 -/
theorem normalized_frobenius_length_tendsto_towerLengthOn_quotient
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [instTower : Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (H : Ideal D) (hH : H.radical = maximalIdeal D) :
    Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ H.map (iterateFrobenius D p n)) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop
      (nhds ((towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸ H.map (algebraMap D (PerfectClosure D p))))) := by
  have heq : instTower = towerPerfectionAlgebra A D p t := by
    apply Algebra.algebra_ext
    intro x
    exact AlgHom.congr_fun (towerToPerfect_unique A (PerfectClosure D p) t p
      (IsScalarTower.toAlgHom A (Tower A t p) (PerfectClosure D p))) x
  subst instTower
  have hbase : ∀ a : A, algebraMap A (PerfectClosure D p) a =
      PerfectClosure.of D p (algebraMap A D a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply A D (PerfectClosure D p), hcanonical]
  have hI : H.map (algebraMap D (PerfectClosure D p)) = H.map (PerfectClosure.of D p) := by
    rw [hcanonical]
  rw [hI]
  exact normalized_frobenius_length_tendsto_perfection_quotient_of_primary
    A D p t hbase ht hdimA hdimD hpos hinj hres hsep H hH

set_option backward.isDefEq.respectTransparency false in
/-- 高次 Frobenius Koszul ホモロジーの正規化長さの零への収束から、
perfection のパラメータ商の正規化長さを Hilbert–Samuel 重複度と同定する。
共通分母・有限段の誤差評価・Euler 公式・極限の一意性を組み合わせる。
高次ホモロジーの消滅極限そのものは、この定理の前提として明示する。 -/
theorem towerLengthOn_perfection_parameter_quotient_eq_multiplicity_of_higher_tendsto
    (A D : Type u) [CommRing A] [IsRegularLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra A D] [Module.Finite A D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    [CharP (ResidueField D) p] [PerfectField (ResidueField D)]
    {h : ℕ} (t : Fin h → A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A)
    (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable)
    [Algebra A (PerfectClosure D p)] [Algebra D (PerfectClosure D p)]
    [Algebra (Tower A t p) (PerfectClosure D p)]
    [IsScalarTower A D (PerfectClosure D p)]
    [IsScalarTower A (Tower A t p) (PerfectClosure D p)]
    (hcanonical : algebraMap D (PerfectClosure D p) = PerfectClosure.of D p)
    (z : Fin h → D) (hz : IsSystemOfParameters D z)
    (hlim : ∀ i : ℤ, i < 0 → Filter.Tendsto (fun n : ℕ ↦
      (Module.length D ((koszulComplex (fun j ↦ z j ^ (p ^ n))).homology i) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞)) Filter.atTop (nhds 0)) :
    (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
      ((PerfectClosure D p) ⧸
        Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) =
      ENNReal.ofReal (HilbertSamuel.multiplicity D (Ideal.span (Set.range z)) D : ℝ) := by
  have hlength := normalized_frobenius_length_tendsto_towerLengthOn_quotient
    A D p t ht hdimA hdimD hpos hinj hres hsep hcanonical (Ideal.span (Set.range z)) hz.2
  have he := HilbertSamuel.normalized_parameter_quotient_tendsto_ennreal_of_higher_koszul
    D z hz (fun n ↦ p ^ n) (fun n ↦ pow_pos (Fact.out : p.Prime).pos n)
    (fun i hi ↦ by
      simpa only [stageRank, pow_mul, Nat.cast_pow] using hlim i hi)
  have hstage (n : ℕ) :
      Module.length D (D ⧸ (Ideal.span (Set.range z)).map (iterateFrobenius D p n)) =
        Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ (p ^ n))) := by
    apply congrArg (fun I : Ideal D ↦ Module.length D (D ⧸ I))
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have htarget :
      (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          (Ideal.span (Set.range z)).map (algebraMap D (PerfectClosure D p))) =
      (towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))) := by
    apply congrArg (fun I : Ideal (PerfectClosure D p) ↦
      (towerLengthOn A D hinj t p
        (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
          ((PerfectClosure D p) ⧸ I))
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hlength' : Filter.Tendsto (fun n : ℕ ↦
      (Module.length D (D ⧸ Ideal.span (Set.range fun j ↦ z j ^ (p ^ n))) : ℝ≥0∞) /
        ((p ^ n : ℕ) : ℝ≥0∞) ^ h) Filter.atTop
      (nhds ((towerLengthOn A D hinj t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) (PerfectClosure D p)).len
        ((PerfectClosure D p) ⧸
          Ideal.span (Set.range fun j ↦ algebraMap D (PerfectClosure D p) (z j))))) := by
    simpa only [hstage, htarget, stageRank, pow_mul, Nat.cast_pow] using hlength
  exact tendsto_nhds_unique hlength' he

end SerrePositivity.Section2
