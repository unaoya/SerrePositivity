module

public import SerrePositivity.Paper.Section2.PerfectApproximationLength
public import SerrePositivity.Paper.Section2.TowerLengthOn
public import SerrePositivity.CommutativeAlgebra.PrimaryParameters

/-! # Perfection の商の長さと Frobenius 極限

正則基底の正規性から非零の共通分母を選び、その分母と合わせて有限長の商を作る
`h-1` 個の元を準素イデアル内で選ぶ。既存の近似環の核の誤差評価に適用し、
通常の Frobenius 商の正規化した長さが perfection の商の正規化長さへ収束することを示す。
利用側が分母や誤差評価用の元を与える必要はない。
任意の両立する塔作用は標準作用と一致することを使い、定理2.5の `towerLengthOn` へも移す。

Hilbert–Kunz 極限の値と Hilbert–Samuel 重複度との同定、正次数の Koszul ホモロジーの
消滅はここでは扱わず、定理2.5の残作業として区別する。
正則パラメータと正規化長さの既存の引用入力を使うが、新しい未証明入力はない。
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
      (nhds ((towerLengthOn A D hinj t p (PerfectClosure D p)).len
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

end SerrePositivity.Section2
